import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h11104 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 2 5 (by decide) (by decide) with h11105 | h11105
  · rcases m.htr 0 3 4 (by decide) (by decide) with h11106 | h11106
    · rcases m.htr 0 3 5 (by decide) (by decide) with h11107 | h11107
      · rcases m.htr 0 4 5 (by decide) (by decide) with h11108 | h11108
        · rcases m.htr 1 2 3 (by decide) (by decide) with h11109 | h11109
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11110 | h11110
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11111 | h11111
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11112 | h11112
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11113 | h11113
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11114 | h11114
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11115 | h11115
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11116 | h11116
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11117 | h11117
                          · linarith only [h11104, h11109, h11117, h8661, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h11104, h11108, h11109, h11117, h8661, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h11107, h11116, h8661, hlam]
                      · linarith only [h11106, h11115, h8661, hlam]
                    · linarith only [h11104, h11108, h11114, h6923, h8661, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h11107, h11113, h5135, hlam]
                · linarith only [h11104, h11106, h11109, h11112, h5135, h8661, hc01, hc12, hlam, hphi]
              · linarith only [h11105, h11109, h11111, h8661, hlam]
            · linarith only [h11109, h11110, h8661, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11127 | h11127
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11128 | h11128
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11129 | h11129
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11130 | h11130
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11131 | h11131
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11132 | h11132
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11133 | h11133
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11134 | h11134
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11135 | h11135
                            · rcases h2bigk with h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c | h11136c
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h0, hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h8661, hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11132, h11135, hc02, hc45, hlam, hphi, ht0b, ht5b, p11136_1]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h0, h11109, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p11136_1]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11109, hc02, hc23, hlam, hphi, p11136_1]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11109, hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11109, h11132, h11135, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11136_1]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11109, h11133, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p11136_1]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11104, h11132, h11135, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11136_1]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p11136_1]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11132, h11135, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11136_1]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                rcases p11136_3 (m.d 0 2) (by simp) with h11151 | h11151
                                · linarith only [h11151, h8661, hlam]
                                · linarith only [h11105, h11151, hlam]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11104, hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11127, hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11132, hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11104, h11133, h11135, hc02, hc45, hlam, hphi, ht0b, ht5b, p11136_1]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11105, hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11128, hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11133, hlam, p11136_0]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [h11134, hlam, p11136_1]
                              · have p11136_0 := h11136c.1
                                have p11136_1 := h11136c.2.1
                                have p11136_2 := h11136c.2.2.1
                                have p11136_3 := h11136c.2.2.2
                                linarith only [hlam, p11136_0]
                            · linarith only [h0, h11104, h11109, h11134, h11135, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11165 | h11165
                            · linarith only [h11132, h11134, h11165, hlam]
                            · rcases h2bigk with h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h0, hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h8661, hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h0, h11109, h11132, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11167_1]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h0, h11109, h11132, h11134, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11167_1]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11109, hc02, hc23, hlam, hphi, p11167_1]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11109, hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11109, h11132, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11167_1]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11109, h11132, h11134, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11167_1]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11104, h11108, h11132, h11134, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11167_1]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p11167_1]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                rcases p11167_3 (m.d 0 2) (by simp) with h11181 | h11181
                                · linarith only [h11181, h8661, hlam]
                                · linarith only [h11104, h11181, hlam]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                rcases p11167_3 (m.d 0 2) (by simp) with h11184 | h11184
                                · linarith only [h11184, h8661, hlam]
                                · linarith only [h11105, h11184, hlam]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11104, hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11127, hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11132, hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11134, hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11105, hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11128, hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11133, hlam, p11167_0]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [h11105, h11132, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p11167_1]
                              · have p11167_0 := h11167c.1
                                have p11167_1 := h11167c.2.1
                                have p11167_2 := h11167c.2.2.1
                                have p11167_3 := h11167c.2.2.2
                                linarith only [hlam, p11167_0]
                        · linarith only [h0, h11109, h11133, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h11109, h11132, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h11104, h11108, h11109, h11131, h6923, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h11104, h11107, h11108, h11109, h11130, h5135, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h11106, h11129, h5135, hlam]
              · linarith only [h0, h11105, h11128, hlam]
            · linarith only [h0, h11104, h11127, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h11204 | h11204
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11205 | h11205
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11206 | h11206
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11207 | h11207
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11208 | h11208
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11209 | h11209
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11210 | h11210
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11211 | h11211
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11212 | h11212
                          · linarith only [h11104, h11108, h11204, h11212, h8661, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11214 | h11214
                            · linarith only [h11105, h11108, h11204, h11210, h11212, h11214, h6923, h8661, hc01, hc12, hlam, hphi]
                            · rcases h2bigk with h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c | h11216c
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h0, hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h8661, hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11204, h8661, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11216_1]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11204, h8661, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p11216_1]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p11216_1]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11105, h7870, h8661, hc01, hc12, hlam, hphi, p11216_1]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                rcases p11216_3 (m.d 0 2) (by simp) with h11225 | h11225
                                · linarith only [h0, h11225, hlam]
                                · linarith only [h11104, h11225, hlam]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                rcases p11216_3 (m.d 0 2) (by simp) with h11228 | h11228
                                · linarith only [h0, h11228, hlam]
                                · linarith only [h11105, h11228, hlam]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11105, h11210, h11212, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11216_1]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11204, hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11204, h11210, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11216_1]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11204, h11210, h11212, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11216_1]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11104, hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11205, hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11210, hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11212, hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11105, hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11206, hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11211, hlam, p11216_0]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [h11105, h11210, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p11216_1]
                              · have p11216_0 := h11216c.1
                                have p11216_1 := h11216c.2.1
                                have p11216_2 := h11216c.2.2.1
                                have p11216_3 := h11216c.2.2.2
                                linarith only [hlam, p11216_0]
                        · linarith only [h11107, h11211, h8661, hlam]
                      · linarith only [h11106, h11210, h8661, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11248 | h11248
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11249 | h11249
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11250 | h11250
                          · linarith only [h11104, h11209, h11250, h8661, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11252 | h11252
                            · linarith only [h11209, h11252, h6923, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h2bigk with h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h0, hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h8661, hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11204, h8661, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11254_1]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11204, h8661, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p11254_1]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p11254_1]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h5135, h8661, hc01, hc12, hlam, hphi, p11254_1]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                rcases p11254_3 (m.d 0 2) (by simp) with h11263 | h11263
                                · linarith only [h0, h11263, hlam]
                                · linarith only [h11104, h11263, hlam]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                rcases p11254_3 (m.d 0 2) (by simp) with h11266 | h11266
                                · linarith only [h0, h11266, hlam]
                                · linarith only [h11105, h11266, hlam]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11105, h11248, h11250, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11254_1]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11204, hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11204, h11248, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11254_1]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11204, h11248, h11250, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11254_1]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11104, hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11205, hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11248, hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11250, hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11105, hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11206, hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11249, hlam, p11254_0]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [h11105, h11248, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p11254_1]
                              · have p11254_0 := h11254c.1
                                have p11254_1 := h11254c.2.1
                                have p11254_2 := h11254c.2.2.1
                                have p11254_3 := h11254c.2.2.2
                                linarith only [hlam, p11254_0]
                        · linarith only [h11107, h11249, h8661, hlam]
                      · linarith only [h11106, h11248, h8661, hlam]
                  · linarith only [h11105, h11107, h11208, h5135, h8661, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h11104, h11106, h11204, h11207, h8661, hlam]
              · linarith only [h11204, h11206, h8661, hc02, hc25, hlam, hphi]
            · linarith only [h11105, h11108, h11204, h11205, h6923, h8661, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11290 | h11290
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11291 | h11291
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11292 | h11292
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11293 | h11293
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11294 | h11294
                    · linarith only [h11108, h11204, h11290, h11294, h6923, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11296 | h11296
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11297 | h11297
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11298 | h11298
                          · linarith only [h0, h11104, h11204, h11294, h11298, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11300 | h11300
                            · linarith only [h11294, h11300, h6923, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h2bigk with h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c | h11302c
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h0, hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h8661, hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h0, h11204, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11302_1]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h0, h11204, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p11302_1]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11204, hc02, hc23, hlam, hphi, p11302_1]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11204, hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11204, h11296, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11302_1]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11204, h11297, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p11302_1]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11105, h11108, h6923, hc01, hc23, hlam, hphi, ht12, p11302_1]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p11302_1]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                rcases p11302_3 (m.d 0 2) (by simp) with h11316 | h11316
                                · linarith only [h11316, h8661, hlam]
                                · linarith only [h11104, h11316, hlam]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                rcases p11302_3 (m.d 0 2) (by simp) with h11319 | h11319
                                · linarith only [h11319, h8661, hlam]
                                · linarith only [h11105, h11319, hlam]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11104, hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11290, hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11296, hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11298, hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11105, hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11291, hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11297, hlam, p11302_0]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [h11105, h11296, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p11302_1]
                              · have p11302_0 := h11302c.1
                                have p11302_1 := h11302c.2.1
                                have p11302_2 := h11302c.2.2.1
                                have p11302_3 := h11302c.2.2.2
                                linarith only [hlam, p11302_0]
                        · linarith only [h11105, h11107, h11297, h5135, h8661, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h11204, h11296, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h11107, h11204, h11291, h11293, h5135, h7870, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h11106, h11292, h5135, hlam]
              · linarith only [h0, h11105, h11291, hlam]
            · linarith only [h0, h11104, h11290, hlam]
      · linarith only [h11105, h11107, h8661, hlam]
    · linarith only [h11104, h11106, h8661, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h11340 | h11340
    · rcases m.htr 0 3 5 (by decide) (by decide) with h11341 | h11341
      · rcases m.htr 0 4 5 (by decide) (by decide) with h11342 | h11342
        · linarith only [h11104, h11105, h11342, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h11344 | h11344
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11345 | h11345
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11346 | h11346
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11347 | h11347
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11348 | h11348
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11349 | h11349
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11350 | h11350
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11351 | h11351
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11352 | h11352
                          · linarith only [h11104, h11105, h11342, h11344, h11351, h11352, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11354 | h11354
                            · linarith only [h11104, h11105, h11350, h11352, h11354, hlam]
                            · rcases h2bigk with h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c | h11356c
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h0, hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h8661, hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11105, h11344, h11347, h11349, h11352, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11356_1]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11105, hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p11356_1]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11104, h11350, h8661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11356_1]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                rcases p11356_3 (m.d 0 2) (by simp) with h11365 | h11365
                                · linarith only [h0, h11365, hlam]
                                · linarith only [h11104, h11365, hlam]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11104, h11105, h11350, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11356_1]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11104, h11350, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11356_1]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11344, hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11344, h11350, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11356_1]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11104, h11105, h11344, h11350, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11356_1]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11104, hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11345, hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11350, hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11352, hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11104, h11350, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11356_1]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11346, hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11351, hlam, p11356_0]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [h11344, h11347, h11349, h11350, h11352, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11356_1]
                              · have p11356_0 := h11356c.1
                                have p11356_1 := h11356c.2.1
                                have p11356_2 := h11356c.2.2.1
                                have p11356_3 := h11356c.2.2.2
                                linarith only [hlam, p11356_0]
                        · linarith only [h11104, h11341, h11344, h11350, h11351, h5135, h8661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h11340, h11350, h8661, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11386 | h11386
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11387 | h11387
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11388 | h11388
                          · linarith only [h11104, h11349, h11388, h6923, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11390 | h11390
                            · linarith only [h11104, h11105, h11344, h11349, h11386, h11387, h11390, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases h2bigk with h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c | h11392c
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h0, hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h8661, hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11105, h11344, h11387, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11392_1]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11105, hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p11392_1]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11341, h8661, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p11392_1]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                rcases p11392_3 (m.d 0 2) (by simp) with h11401 | h11401
                                · linarith only [h0, h11401, hlam]
                                · linarith only [h11104, h11401, hlam]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11104, h11105, h11386, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11392_1]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11104, h11386, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11392_1]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11344, hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11344, h11386, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11392_1]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11104, h11105, h11344, h11386, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11392_1]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11104, hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11345, hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11386, hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11388, hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11104, h11346, h11386, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11392_1]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11346, hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11387, hlam, p11392_0]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [h11344, h11386, h11387, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11392_1]
                              · have p11392_0 := h11392c.1
                                have p11392_1 := h11392c.2.1
                                have p11392_2 := h11392c.2.2.1
                                have p11392_3 := h11392c.2.2.2
                                linarith only [hlam, p11392_0]
                        · linarith only [h11104, h11341, h11344, h11386, h11387, h5135, h8661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h11340, h11386, h8661, hlam]
                  · linarith only [h11341, h11348, h5135, hlam]
                · linarith only [h11104, h11340, h11344, h11347, h8661, hlam]
              · linarith only [h11104, h11344, h11346, h8661, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h11104, h11344, h11345, h8661, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11426 | h11426
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11427 | h11427
              · linarith only [h11105, h11344, h11427, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11429 | h11429
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11430 | h11430
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11431 | h11431
                    · linarith only [h11342, h11344, h11426, h11431, h6923, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11433 | h11433
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11434 | h11434
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11435 | h11435
                          · linarith only [h0, h11104, h11427, h11431, h11434, h11435, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11437 | h11437
                            · linarith only [h0, h11427, h11435, h11437, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h2bigk with h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c | h11439c
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h0, hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h8661, hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h0, h11427, h11434, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11439_1]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11105, hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11427, h11434, hc02, hc23, hlam, hphi, p11439_1]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11344, hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11427, h11433, h11435, hc34, hc45, hlam, hphi, p11439_1]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11427, hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11104, h11433, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11439_1]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p11439_1]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                rcases p11439_3 (m.d 0 2) (by simp) with h11453 | h11453
                                · linarith only [h11453, h8661, hlam]
                                · linarith only [h11104, h11453, hlam]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11427, h7870, hc01, hc23, hlam, hphi, ht12, p11439_1]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11104, hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11426, hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11433, hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11435, hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11104, h11433, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11439_1]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11426, h6923, hc01, hc25, hlam, hphi, ht12, p11439_1]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11434, hlam, p11439_0]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [h11433, h11435, hc34, hc45, hlam, hphi, p11439_1]
                              · have p11439_0 := h11439c.1
                                have p11439_1 := h11439c.2.1
                                have p11439_2 := h11439c.2.2.1
                                have p11439_3 := h11439c.2.2.2
                                linarith only [hlam, p11439_0]
                        · linarith only [h11341, h11344, h11434, h5135, hlam]
                      · linarith only [h11344, h11426, h11433, h6923, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h11341, h11430, h5135, hlam]
                · linarith only [h0, h11104, h11340, h11344, h11429, h5135, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h11104, h11426, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h11472 | h11472
        · linarith only [h11104, h11341, h11472, h8661, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h11474 | h11474
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11475 | h11475
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11476 | h11476
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11477 | h11477
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11478 | h11478
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11479 | h11479
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11480 | h11480
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11481 | h11481
                        · linarith only [h11104, h11341, h11474, h11480, h11481, h8661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h11104, h11474, h11478, h11480, h11481, h8661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h11340, h11480, h8661, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11485 | h11485
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11486 | h11486
                        · linarith only [h11341, h11474, h11486, h5135, hc01, hc12, hlam, hphi]
                        · linarith only [h11104, h11474, h11478, h11485, h11486, h8661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h11340, h11485, h8661, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11490 | h11490
                    · linarith only [h11472, h11477, h11478, h11490, h6923, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11492 | h11492
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11493 | h11493
                        · linarith only [h11474, h11478, h11493, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11495 | h11495
                          · linarith only [h0, h11104, h11490, h11495, h7870, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11497 | h11497
                            · linarith only [h11104, h11490, h11492, h11497, h6923, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · linarith only [h11104, h11474, h11478, h11492, h11497, h8661, hc34, hc45, hlam, hphi]
                      · linarith only [h11340, h11492, h8661, hlam]
                · linarith only [h11104, h11340, h11474, h11477, h8661, hlam]
              · linarith only [h11104, h11474, h11476, h8661, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h11104, h11474, h11475, h8661, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11504 | h11504
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11505 | h11505
              · linarith only [h11104, h11105, h11474, h11505, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11507 | h11507
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11508 | h11508
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11509 | h11509
                    · linarith only [h11472, h11474, h11504, h11509, h6923, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11511 | h11511
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11512 | h11512
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11513 | h11513
                          · linarith only [h0, h11104, h11505, h11509, h11512, h11513, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11515 | h11515
                            · linarith only [h11104, h11341, h11474, h11505, h11508, h11511, h11513, h11515, h8661, hc12, hc23, hlam, hphi]
                            · rcases h2bigk with h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c | h11517c
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h0, hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h8661, hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11341, h11474, h11508, h11511, h8661, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11517_1]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11105, hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11505, hc02, hc25, hlam, hphi, p11517_1]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11474, hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11505, h11511, h11513, hc34, hc45, hlam, hphi, p11517_1]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11505, hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11104, h11511, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11517_1]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p11517_1]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                rcases p11517_3 (m.d 0 2) (by simp) with h11531 | h11531
                                · linarith only [h11531, h8661, hlam]
                                · linarith only [h11104, h11531, hlam]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11104, h11105, h11511, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11517_1]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11104, hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11504, hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11511, hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11513, hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11104, h11511, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11517_1]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11504, h6923, hc01, hc25, hlam, hphi, ht12, p11517_1]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11512, hlam, p11517_0]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [h11511, h11513, hc34, hc45, hlam, hphi, p11517_1]
                              · have p11517_0 := h11517c.1
                                have p11517_1 := h11517c.2.1
                                have p11517_2 := h11517c.2.2.1
                                have p11517_3 := h11517c.2.2.2
                                linarith only [hlam, p11517_0]
                        · linarith only [h11474, h11508, h11512, hlam]
                      · linarith only [h11341, h11474, h11508, h11511, hc03, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11547 | h11547
                    · linarith only [h11472, h11474, h11504, h11547, h6923, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11549 | h11549
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11550 | h11550
                        · linarith only [h0, h11474, h11508, h11550, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h11474, h11504, h11550, h6923, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h11474, h11504, h11549, h6923, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h11104, h11340, h11507, h5135, h8661, hlam]
            · linarith only [h0, h11104, h11504, h5135, h8661, hc01, hc13, hlam, hphi]
    · linarith only [h11104, h11340, h8661, hlam]

set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h11104 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h11557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 3 4 (by decide) (by decide) with h11558 | h11558
  · rcases m.htr 0 3 5 (by decide) (by decide) with h11559 | h11559
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11560 | h11560
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11561 | h11561
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11562 | h11562
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11563 | h11563
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11564 | h11564
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11565 | h11565
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11566 | h11566
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11567 | h11567
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11568 | h11568
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11569 | h11569
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11570 | h11570
                          · rcases h2bigk with h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c | h11571c
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h0, hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h8661, hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11104, hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11104, h11561, h11567, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p11571_1]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p11571_1]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11557, h7870, h8661, hc01, hc12, hlam, hphi, p11571_1]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11104, h11557, h11568, h11570, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11571_1]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              rcases p11571_3 (m.d 0 2) (by simp) with h11581 | h11581
                              · linarith only [h0, h11581, hlam]
                              · linarith only [h11557, h11581, hlam]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11557, h11568, h11570, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11571_1]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11561, hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11104, h11557, h11561, h11568, h11570, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11571_1]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11561, h11568, h11570, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11571_1]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11557, h11568, h11570, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11571_1]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11562, hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11567, hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11561, h11567, h11568, h11570, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11571_1]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11557, hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11563, hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11568, hlam, p11571_0]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [h11569, hlam, p11571_1]
                            · have p11571_0 := h11571c.1
                              have p11571_1 := h11571c.2.1
                              have p11571_2 := h11571c.2.2.1
                              have p11571_3 := h11571c.2.2.2
                              linarith only [hlam, p11571_0]
                          · linarith only [h11104, h11557, h11561, h11567, h11569, h11570, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h11104, h11557, h11560, h11569, hlam]
                      · linarith only [h11559, h11568, h8661, hlam]
                    · linarith only [h11558, h11567, h8661, hlam]
                  · linarith only [h11104, h11557, h11560, h11566, h6923, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h11104, h11557, h11559, h11562, h11565, h5135, hc01, hc14, hlam, hphi]
              · linarith only [h11558, h11561, h11564, h8661, hlam]
            · linarith only [h11561, h11563, h8661, hc02, hc25, hlam, hphi]
          · linarith only [h11557, h11561, h11562, h7870, h8661, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11608 | h11608
          · linarith only [h11104, h11557, h11561, h11608, h7870, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11610 | h11610
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11611 | h11611
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11612 | h11612
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11613 | h11613
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11614 | h11614
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11615 | h11615
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11616 | h11616
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11617 | h11617
                          · rcases h2bigk with h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c | h11618c
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h0, hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h8661, hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11104, hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h0, h11608, h11614, h11615, h11617, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11618_1]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11608, h11614, hc02, hc23, hlam, hphi, p11618_1]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11561, hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11608, hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11608, h11614, h11615, h11617, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11618_1]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11557, h11615, h11617, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11618_1]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p11618_1]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11104, h11557, h11615, h11617, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11618_1]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              rcases p11618_3 (m.d 0 2) (by simp) with h11633 | h11633
                              · linarith only [h11633, h8661, hlam]
                              · linarith only [h11557, h11633, hlam]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11557, h11615, h11617, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11618_1]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11610, h7870, hc01, hc24, hlam, hphi, ht12, p11618_1]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11614, hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              rcases p11618_3 (m.d 0 2) (by simp) with h11640 | h11640
                              · linarith only [h11104, h11640, hlam]
                              · linarith only [h11557, h11640, hlam]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11557, hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11610, hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11615, hlam, p11618_0]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [h11616, hlam, p11618_1]
                            · have p11618_0 := h11618c.1
                              have p11618_1 := h11618c.2.1
                              have p11618_2 := h11618c.2.2.1
                              have p11618_3 := h11618c.2.2.2
                              linarith only [hlam, p11618_0]
                          · rcases h2bigk with h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c | h11648c
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h0, hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h8661, hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11104, hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h8661, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p11648_1]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p11648_1]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11561, hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11608, hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11608, h11614, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p11648_1]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11557, h11560, h11617, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11648_1]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p11648_1]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11104, h11557, h11560, h11617, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11648_1]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11616, h11617, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11648_1]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [hc02, hc24, hlam, hphi, p11648_1]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11610, h7870, hc01, hc24, hlam, hphi, ht12, p11648_1]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11614, hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11614, h11616, h11617, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11648_1]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11557, hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11610, hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11615, hlam, p11648_0]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [h11616, hlam, p11648_1]
                            · have p11648_0 := h11648c.1
                              have p11648_1 := h11648c.2.1
                              have p11648_2 := h11648c.2.2.1
                              have p11648_3 := h11648c.2.2.2
                              linarith only [hlam, p11648_0]
                        · linarith only [h11104, h11560, h11616, hlam]
                      · linarith only [h11559, h11561, h11615, h5135, hlam]
                    · linarith only [h11558, h11561, h11614, h5135, hlam]
                  · linarith only [h11560, h11561, h11610, h11613, h6923, h7870, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h11559, h11612, h5135, hlam]
              · linarith only [h11558, h11611, h5135, hlam]
            · linarith only [h0, h11104, h11557, h11610, h6923, hc01, hc14, hlam, hphi]
      · linarith only [h11104, h11557, h11560, hlam]
    · linarith only [h11104, h11557, h11558, h11559, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h11683 | h11683
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11684 | h11684
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11685 | h11685
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11686 | h11686
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11687 | h11687
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11688 | h11688
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11689 | h11689
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11690 | h11690
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11691 | h11691
                    · linarith only [h11557, h11558, h11685, h11691, h8661, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h11557, h11685, h11688, h11691, h8661, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h11684, h11690, h6923, hlam]
                · linarith only [h11683, h11689, h5135, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11696 | h11696
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11697 | h11697
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11698 | h11698
                    · linarith only [h11685, h11688, h11698, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11700 | h11700
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11701 | h11701
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11702 | h11702
                          · rcases h2bigk with h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [hlam, p11703_0]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h0, hlam, p11703_0]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h8661, hlam, p11703_0]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11104, hlam, p11703_0]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11685, h11688, h11700, h11702, h8661, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11703_1]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p11703_1]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [hlam, p11703_0]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h5135, h8661, hc01, hc12, hlam, hphi, p11703_1]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11104, h11557, h11700, h11702, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11703_1]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              rcases p11703_3 (m.d 0 2) (by simp) with h11713 | h11713
                              · linarith only [h0, h11713, hlam]
                              · linarith only [h11557, h11713, hlam]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11557, h11700, h11702, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11703_1]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11685, hlam, p11703_0]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [hlam, p11703_0]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11698, hlam, p11703_1]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11685, h11688, h11700, h11702, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11703_1]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11557, h11686, h11700, h11702, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p11703_1]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11686, hlam, p11703_0]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11703_1]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [hlam, p11703_0]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11686, h11700, h11702, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11703_1]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11557, hlam, p11703_0]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11687, hlam, p11703_0]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11700, hlam, p11703_0]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [h11701, hlam, p11703_1]
                            · have p11703_0 := h11703c.1
                              have p11703_1 := h11703c.2.1
                              have p11703_2 := h11703c.2.2.1
                              have p11703_3 := h11703c.2.2.2
                              linarith only [hlam, p11703_0]
                          · linarith only [h11557, h11685, h11688, h11700, h11702, h8661, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h11104, h11557, h11684, h11700, h11701, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h11557, h11683, h11700, h8661, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h11557, h11684, h11685, h11697, h6923, h8661, hc01, hc13, hlam, hphi]
                · linarith only [h11557, h11683, h11685, h11696, h8661, hlam]
            · linarith only [h11557, h11687, h8661, hc12, hc23, hlam, hphi]
          · linarith only [h11685, h11686, h8661, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11738 | h11738
          · linarith only [h11104, h11557, h11685, h11738, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11740 | h11740
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11741 | h11741
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11742 | h11742
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11743 | h11743
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11744 | h11744
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11745 | h11745
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11746 | h11746
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11747 | h11747
                          · rcases h2bigk with h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c | h11748c
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h0, hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h8661, hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11104, hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11558, h11745, h11747, h8661, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11748_1]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11738, h11744, hc02, hc23, hlam, hphi, p11748_1]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11685, hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11738, hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11738, h11744, h11745, h11747, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11748_1]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11557, h11745, h11747, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11748_1]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p11748_1]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11104, h11557, h11745, h11747, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11748_1]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              rcases p11748_3 (m.d 0 2) (by simp) with h11763 | h11763
                              · linarith only [h11763, h8661, hlam]
                              · linarith only [h11557, h11763, hlam]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11557, h11745, h11747, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11748_1]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11740, h7870, hc01, hc24, hlam, hphi, ht12, p11748_1]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11744, hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              rcases p11748_3 (m.d 0 2) (by simp) with h11770 | h11770
                              · linarith only [h11104, h11770, hlam]
                              · linarith only [h11557, h11770, hlam]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11557, hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11740, hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11745, hlam, p11748_0]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [h11746, hlam, p11748_1]
                            · have p11748_0 := h11748c.1
                              have p11748_1 := h11748c.2.1
                              have p11748_2 := h11748c.2.2.1
                              have p11748_3 := h11748c.2.2.2
                              linarith only [hlam, p11748_0]
                          · linarith only [h11557, h11558, h11684, h11745, h11747, h8661, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h11738, h11746, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h11558, h11683, h11685, h11741, h11745, hlam]
                    · linarith only [h11685, h11741, h11744, hlam]
                  · linarith only [h11557, h11558, h11684, h11685, h11741, h11743, h6923, h8661, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h11558, h11683, h11741, h11742, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11784 | h11784
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11785 | h11785
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11786 | h11786
                    · linarith only [h11685, h11740, h11741, h11786, h7870, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h11685, h11740, h11786, h7870, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h11557, h11684, h11685, h11785, h6923, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h11683, h11784, h5135, hlam]
            · linarith only [h0, h11557, h11740, h5135, h8661, hc01, hc13, hlam, hphi]
      · linarith only [h11557, h11558, h11684, h8661, hlam]
    · linarith only [h11557, h11683, h8661, hlam]

end R2N4
