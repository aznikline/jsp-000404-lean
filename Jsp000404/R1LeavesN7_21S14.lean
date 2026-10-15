import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
    · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
      · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
        · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
          · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
              · linarith only [h0, h15, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h12, h15, h17, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h12, h15, h19, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · linarith only [h0, h12, h14, h19, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
              · linarith only [h0, h22, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                · linarith only [h0, h12, h14, h22, h24, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                  · linarith only [h0, h14, h26, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                    · linarith only [h0, h12, h14, h28, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                    · rcases h1bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h10, hc01, hlam, hphi, ht0b, ht45, ht5b, p30_1, u4ehi2]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h12, h22, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        rcases p30_3 (m.d 0 1) (by simp) with h34 | h34
                        · rcases p30_3 (m.d 1 2) (by simp) with h35 | h35
                          · linarith only [h0, h35, hlam]
                          · linarith only [h10, h35, hlam]
                        · linarith only [h34, hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        rcases p30_3 (m.d 0 1) (by simp) with h39 | h39
                        · rcases p30_3 (m.d 1 2) (by simp) with h40 | h40
                          · linarith only [h0, h40, hlam]
                          · linarith only [h11, h40, hlam]
                        · linarith only [h39, hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h0, hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h13, h24, h26, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p30_1, u4ehi2]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h0, h12, h22, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h0, h13, h24, h26, hc01, hlam, hphi, ht0b, ht45, ht5b, p30_1, u4ehi2]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h1, hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h9, hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h1, h12, h22, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h0, h13, h24, h26, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p30_1, u4ehi2]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h2, hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h10, hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h12, hlam, p30_1]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h14, hlam, p30_1]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h3, hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h11, hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h13, hlam, p30_0]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [h12, h22, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1]
                      · have p30_0 := h30c.1
                        have p30_1 := h30c.2.1
                        have p30_2 := h30c.2.2.1
                        have p30_3 := h30c.2.2.2
                        linarith only [hlam, p30_0]
          · linarith only [h0, h12, h13, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
          · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
            · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
              · linarith only [h12, h65, h67, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h69 | h69
                · linarith only [h0, h69, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                · linarith only [h12, h65, h69, hc23, hc34, hlam, hphi]
            · linarith only [h0, h12, h5, h65, h66, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
            · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
              · linarith only [h0, h12, h74, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h76 | h76
                · linarith only [h65, h76, h9, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                  · linarith only [h0, h10, h78, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h2, h73, h78, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
              · linarith only [h0, h81, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                · linarith only [h0, h65, h83, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                  · linarith only [h10, h73, h85, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
                    · rcases h1bigk with h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h10, hc01, hlam, hphi, ht0b, ht45, ht5b, p88_1, u4ehi2]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        rcases p88_3 (m.d 0 1) (by simp) with h91 | h91
                        · rcases p88_3 (m.d 1 2) (by simp) with h92 | h92
                          · linarith only [h0, h92, hlam]
                          · linarith only [h9, h92, hlam]
                        · linarith only [h91, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        rcases p88_3 (m.d 0 1) (by simp) with h96 | h96
                        · rcases p88_3 (m.d 1 2) (by simp) with h97 | h97
                          · linarith only [h0, h97, hlam]
                          · linarith only [h10, h97, hlam]
                        · linarith only [h96, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        rcases p88_3 (m.d 0 1) (by simp) with h101 | h101
                        · rcases p88_3 (m.d 1 2) (by simp) with h102 | h102
                          · linarith only [h0, h102, hlam]
                          · linarith only [h102, h11, hlam]
                        · linarith only [h101, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h0, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        rcases p88_3 (m.d 0 1) (by simp) with h108 | h108
                        · rcases p88_3 (m.d 1 2) (by simp) with h109 | h109
                          · rcases p88_3 (m.d 1 3) (by simp) with h110 | h110
                            · linarith only [h110, h9, hlam]
                            · rcases p88_3 (m.d 1 4) (by simp) with h112 | h112
                              · linarith only [h10, h112, hlam]
                              · linarith only [h112, h12, hlam]
                          · linarith only [h109, h9, hlam]
                        · linarith only [h1, h108, hlam]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p88_1, u4ehi1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p88_1, u5ehi1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h1, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h9, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h12, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h65, hlam, p88_1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h2, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h10, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h73, h87, h9, hc23, hc34, hlam, hphi, p88_1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h73, hlam, p88_1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h3, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h11, hlam, p88_0]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h73, h87, h9, hc23, hc34, hlam, hphi, p88_1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [h73, h87, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p88_1, u4ehi1]
                      · have p88_0 := h88c.1
                        have p88_1 := h88c.2.1
                        have p88_2 := h88c.2.2.1
                        have p88_3 := h88c.2.2.2
                        linarith only [hlam, p88_0]
                    · rcases h1bigk with h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h10, hc01, hlam, hphi, ht0b, ht45, ht5b, p134_1, u4ehi2]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h0, h12, h5, h8, h87, hlam, p134_2]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        rcases p134_3 (m.d 0 1) (by simp) with h138 | h138
                        · rcases p134_3 (m.d 1 2) (by simp) with h139 | h139
                          · linarith only [h0, h139, hlam]
                          · linarith only [h10, h139, hlam]
                        · linarith only [h138, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        rcases p134_3 (m.d 0 1) (by simp) with h143 | h143
                        · rcases p134_3 (m.d 1 2) (by simp) with h144 | h144
                          · linarith only [h0, h144, hlam]
                          · linarith only [h11, h144, hlam]
                        · linarith only [h143, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h0, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        rcases p134_3 (m.d 0 1) (by simp) with h150 | h150
                        · rcases p134_3 (m.d 1 2) (by simp) with h151 | h151
                          · rcases p134_3 (m.d 1 3) (by simp) with h152 | h152
                            · linarith only [h152, h9, hlam]
                            · rcases p134_3 (m.d 1 4) (by simp) with h154 | h154
                              · linarith only [h10, h154, hlam]
                              · linarith only [h12, h154, hlam]
                          · linarith only [h151, h9, hlam]
                        · linarith only [h1, h150, hlam]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht45, ht5b, p134_1, u4ehi2]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p134_1, u5ehi1]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h1, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h9, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h12, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h65, hlam, p134_1]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h2, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h10, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h0, h12, h5, h8, h87, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p134_1]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h73, hlam, p134_1]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h3, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h11, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        rcases p134_3 (m.d 0 1) (by simp) with h173 | h173
                        · rcases p134_3 (m.d 1 2) (by simp) with h174 | h174
                          · rcases p134_3 (m.d 1 3) (by simp) with h175 | h175
                            · linarith only [h175, h65, hlam]
                            · rcases p134_3 (m.d 1 4) (by simp) with h177 | h177
                              · linarith only [h177, h73, hlam]
                              · linarith only [h12, h177, hlam]
                          · linarith only [h174, h9, hlam]
                        · linarith only [h1, h173, hlam]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p134_1, u4ehi1]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [hlam, p134_0]
      · linarith only [h0, h10, h11, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
      · linarith only [h0, h10, h185, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
        · linarith only [h0, h10, h187, h5, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h189 | h189
          · linarith only [h0, h10, h189, h5, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h191 | h191
            · rcases m.htr 2 3 4 (by decide) (by decide) with h192 | h192
              · linarith only [h0, h10, h187, h192, h5, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                · linarith only [h0, h10, h194, h5, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h196 | h196
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h197 | h197
                    · rcases h1bigk with h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        rcases p198_3 (m.d 0 1) (by simp) with h200 | h200
                        · rcases p198_3 (m.d 1 2) (by simp) with h201 | h201
                          · linarith only [h201, hlam, p198_0]
                          · rcases p198_3 (m.d 1 3) (by simp) with h203 | h203
                            · linarith only [h1, h203, hlam]
                            · rcases p198_3 (m.d 1 4) (by simp) with h205 | h205
                              · linarith only [h2, h205, hlam]
                              · linarith only [h10, h205, hlam]
                        · linarith only [h200, hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        rcases p198_3 (m.d 0 1) (by simp) with h209 | h209
                        · rcases p198_3 (m.d 1 2) (by simp) with h210 | h210
                          · linarith only [h0, h210, hlam]
                          · linarith only [h210, h9, hlam]
                        · linarith only [h209, hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h191, hc01, hlam, hphi, ht0b, ht45, ht5b, p198_1, u4ehi4]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        rcases p198_3 (m.d 0 1) (by simp) with h215 | h215
                        · rcases p198_3 (m.d 1 2) (by simp) with h216 | h216
                          · linarith only [h0, h216, hlam]
                          · rcases p198_3 (m.d 1 3) (by simp) with h218 | h218
                            · linarith only [h1, h218, hlam]
                            · rcases p198_3 (m.d 1 4) (by simp) with h220 | h220
                              · linarith only [h2, h220, hlam]
                              · linarith only [h191, h220, hlam]
                        · linarith only [h215, hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h0, hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h0, h185, h194, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p198_1]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h10, hlam, p198_1]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h185, hlam, p198_1]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h1, hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h9, hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h187, hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h189, hlam, p198_1]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h2, hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h2, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p198_1]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        rcases p198_3 (m.d 0 1) (by simp) with h236 | h236
                        · rcases p198_3 (m.d 1 2) (by simp) with h237 | h237
                          · linarith only [h10, h237, hlam]
                          · linarith only [h237, h9, hlam]
                        · linarith only [h1, h236, hlam]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h0, h10, h185, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p198_1]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h3, hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p198_1]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        rcases p198_3 (m.d 0 1) (by simp) with h245 | h245
                        · rcases p198_3 (m.d 1 2) (by simp) with h246 | h246
                          · linarith only [h185, h246, hlam]
                          · linarith only [h246, h9, hlam]
                        · linarith only [h1, h245, hlam]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [h191, hlam, p198_0]
                      · have p198_0 := h198c.1
                        have p198_1 := h198c.2.1
                        have p198_2 := h198c.2.2.1
                        have p198_3 := h198c.2.2.2
                        linarith only [hlam, p198_0]
                    · linarith only [h0, h10, h192, h197, h5, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h10, h191, h196, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h254 | h254
              · linarith only [h10, h254, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h256 | h256
                · linarith only [h10, h256, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h258 | h258
                  · linarith only [h0, h10, h191, h258, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h10, h258, h5, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h261 | h261
    · linarith only [h0, h261, h4, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h263 | h263
      · linarith only [h0, h263, h4, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h265 | h265
        · rcases m.htr 1 3 5 (by decide) (by decide) with h266 | h266
          · rcases m.htr 1 4 5 (by decide) (by decide) with h267 | h267
            · rcases m.htr 2 3 4 (by decide) (by decide) with h268 | h268
              · rcases m.htr 2 3 5 (by decide) (by decide) with h269 | h269
                · rcases m.htr 2 4 5 (by decide) (by decide) with h270 | h270
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h271 | h271
                    · linarith only [h1, h265, h271, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h2, h267, h271, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h261, h267, h270, hlam]
                · linarith only [h266, h269, h9, hlam]
              · linarith only [h265, h268, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h277 | h277
              · rcases m.htr 2 3 5 (by decide) (by decide) with h278 | h278
                · rcases m.htr 2 4 5 (by decide) (by decide) with h279 | h279
                  · linarith only [h0, h267, h279, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h281 | h281
                    · linarith only [h261, h263, h265, h267, h279, h281, hc12, hc25, hlam, hphi]
                    · rcases h1bigk with h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [hlam, p283_0]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h0, h261, h279, h5, h8, hlam, p283_2]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h266, hc01, hlam, hphi, ht0b, ht5b, p283_1, u5ehi3]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        rcases p283_3 (m.d 0 1) (by simp) with h287 | h287
                        · rcases p283_3 (m.d 1 2) (by simp) with h288 | h288
                          · linarith only [h0, h288, hlam]
                          · rcases p283_3 (m.d 1 3) (by simp) with h290 | h290
                            · linarith only [h1, h290, hlam]
                            · linarith only [h265, h290, hlam]
                        · linarith only [h287, hlam, p283_0]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        rcases p283_3 (m.d 0 1) (by simp) with h294 | h294
                        · rcases p283_3 (m.d 1 2) (by simp) with h295 | h295
                          · linarith only [h0, h295, hlam]
                          · rcases p283_3 (m.d 1 3) (by simp) with h297 | h297
                            · linarith only [h1, h297, hlam]
                            · linarith only [h266, h297, hlam]
                        · linarith only [h294, hlam, p283_0]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h0, hlam, p283_0]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [hlam, p283_0]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h9, hlam, p283_1]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h261, hlam, p283_1]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h263, hlam, p283_1]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h1, hlam, p283_0]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        rcases p283_3 (m.d 0 1) (by simp) with h307 | h307
                        · rcases p283_3 (m.d 1 2) (by simp) with h308 | h308
                          · linarith only [h308, h9, hlam]
                          · rcases p283_3 (m.d 1 3) (by simp) with h310 | h310
                            · rcases p283_3 (m.d 1 4) (by simp) with h311 | h311
                              · linarith only [h265, h311, hlam]
                              · linarith only [h261, h311, hlam]
                            · linarith only [h310, h9, hlam]
                        · linarith only [h0, h307, hlam]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [hlam, p283_0]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p283_1, u4ehi1]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht5b, p283_1, u5ehi1]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h2, hlam, p283_0]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h0, h261, h279, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p283_1]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h265, hlam, p283_1]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [hlam, p283_0]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h267, hlam, p283_1]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h3, hlam, p283_0]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        rcases p283_3 (m.d 0 1) (by simp) with h325 | h325
                        · rcases p283_3 (m.d 1 2) (by simp) with h326 | h326
                          · linarith only [h263, h326, hlam]
                          · rcases p283_3 (m.d 1 3) (by simp) with h328 | h328
                            · rcases p283_3 (m.d 1 4) (by simp) with h329 | h329
                              · linarith only [h267, h329, hlam]
                              · linarith only [h261, h329, hlam]
                            · linarith only [h328, h9, hlam]
                        · linarith only [h0, h325, hlam]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h266, hlam, p283_0]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p283_1, u4ehi1]
                      · have p283_0 := h283c.1
                        have p283_1 := h283c.2.1
                        have p283_2 := h283c.2.2.1
                        have p283_3 := h283c.2.2.2
                        linarith only [hlam, p283_0]
                · linarith only [h0, h265, h278, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h265, h277, h9, hlam]
          · linarith only [h0, h265, h266, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h340 | h340
          · rcases m.htr 1 4 5 (by decide) (by decide) with h341 | h341
            · rcases m.htr 2 3 4 (by decide) (by decide) with h342 | h342
              · linarith only [h265, h340, h342, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h344 | h344
                · rcases m.htr 2 4 5 (by decide) (by decide) with h345 | h345
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h346 | h346
                    · rcases h1bigk with h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        rcases p347_3 (m.d 0 1) (by simp) with h349 | h349
                        · rcases p347_3 (m.d 1 2) (by simp) with h350 | h350
                          · linarith only [h350, hlam, p347_0]
                          · rcases p347_3 (m.d 1 3) (by simp) with h352 | h352
                            · linarith only [h1, h352, hlam]
                            · linarith only [h352, h9, hlam]
                        · linarith only [h349, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h340, h346, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi4]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h265, h340, h346, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi4]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        rcases p347_3 (m.d 0 1) (by simp) with h358 | h358
                        · rcases p347_3 (m.d 1 2) (by simp) with h359 | h359
                          · linarith only [h0, h359, hlam]
                          · rcases p347_3 (m.d 1 3) (by simp) with h361 | h361
                            · linarith only [h1, h361, hlam]
                            · linarith only [h340, h361, hlam]
                        · linarith only [h358, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h0, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h9, hlam, p347_1]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h261, hlam, p347_1]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h263, hlam, p347_1]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h1, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h342, h9, hc12, hc34, hlam, hphi, ht23, p347_1]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h265, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h342, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p347_1, u5ehi1]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h2, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        rcases p347_3 (m.d 0 1) (by simp) with h376 | h376
                        · rcases p347_3 (m.d 1 2) (by simp) with h377 | h377
                          · linarith only [h261, h377, hlam]
                          · rcases p347_3 (m.d 1 3) (by simp) with h379 | h379
                            · linarith only [h265, h379, hlam]
                            · linarith only [h379, h9, hlam]
                        · linarith only [h0, h376, hlam]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h0, h261, h340, h346, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi4]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h0, h261, h340, h346, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi4]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h3, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h263, h342, h344, hc12, hc34, hlam, hphi, ht23, p347_1]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h340, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h341, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [hlam, p347_0]
                    · linarith only [h0, h342, h344, h346, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · linarith only [h261, h265, h3, h340, h341, h345, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                · linarith only [h261, h265, h340, h344, h9, hc12, hc24, hlam, hphi]
            · linarith only [h0, h265, h340, h341, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h395 | h395
            · rcases m.htr 2 3 4 (by decide) (by decide) with h396 | h396
              · linarith only [h0, h265, h395, h396, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h398 | h398
                · linarith only [h340, h396, h398, h9, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h400 | h400
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h401 | h401
                    · rcases h1bigk with h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [hlam, p402_0]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h0, h398, h4, h7, h9, hlam, p402_2]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        rcases p402_3 (m.d 0 1) (by simp) with h405 | h405
                        · rcases p402_3 (m.d 1 2) (by simp) with h406 | h406
                          · linarith only [h0, h406, hlam]
                          · rcases p402_3 (m.d 1 3) (by simp) with h408 | h408
                            · linarith only [h408, hlam, p402_0]
                            · rcases p402_3 (m.d 1 4) (by simp) with h410 | h410
                              · linarith only [h2, h410, hlam]
                              · linarith only [h265, h410, hlam]
                        · linarith only [h405, hlam, p402_0]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h395, hc01, hlam, hphi, ht0b, ht45, ht5b, p402_1, u4ehi4]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        rcases p402_3 (m.d 0 1) (by simp) with h415 | h415
                        · rcases p402_3 (m.d 1 2) (by simp) with h416 | h416
                          · linarith only [h0, h416, hlam]
                          · rcases p402_3 (m.d 1 3) (by simp) with h418 | h418
                            · linarith only [h1, h418, hlam]
                            · rcases p402_3 (m.d 1 4) (by simp) with h420 | h420
                              · linarith only [h2, h420, hlam]
                              · linarith only [h395, h420, hlam]
                        · linarith only [h415, hlam, p402_0]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h0, hlam, p402_0]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [hlam, p402_0]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h9, hlam, p402_1]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h261, hlam, p402_1]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h263, hlam, p402_1]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h1, hlam, p402_0]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h0, h398, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p402_1]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [hlam, p402_0]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h265, hlam, p402_0]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h340, hlam, p402_1]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h2, hlam, p402_0]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        rcases p402_3 (m.d 0 1) (by simp) with h435 | h435
                        · rcases p402_3 (m.d 1 2) (by simp) with h436 | h436
                          · linarith only [h261, h436, hlam]
                          · rcases p402_3 (m.d 1 3) (by simp) with h438 | h438
                            · linarith only [h265, h438, hlam]
                            · linarith only [h438, h9, hlam]
                        · linarith only [h0, h435, hlam]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        rcases p402_3 (m.d 0 1) (by simp) with h442 | h442
                        · rcases p402_3 (m.d 1 2) (by simp) with h443 | h443
                          · linarith only [h261, h443, hlam]
                          · rcases p402_3 (m.d 1 3) (by simp) with h445 | h445
                            · linarith only [h265, h445, hlam]
                            · rcases p402_3 (m.d 1 4) (by simp) with h447 | h447
                              · rcases p402_3 (m.d 1 5) (by simp) with h448 | h448
                                · linarith only [h395, h448, hlam]
                                · linarith only [h340, h448, hlam]
                              · linarith only [h265, h447, hlam]
                        · linarith only [h1, h442, hlam]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [hlam, p402_0]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h2, h395, hc01, hlam, hphi, ht0b, ht45, ht5b, p402_1, u4ehi4]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h3, hlam, p402_0]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        rcases p402_3 (m.d 0 1) (by simp) with h456 | h456
                        · rcases p402_3 (m.d 1 2) (by simp) with h457 | h457
                          · linarith only [h263, h457, hlam]
                          · rcases p402_3 (m.d 1 3) (by simp) with h459 | h459
                            · linarith only [h340, h459, hlam]
                            · linarith only [h459, h9, hlam]
                        · linarith only [h0, h456, hlam]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        rcases p402_3 (m.d 0 1) (by simp) with h463 | h463
                        · rcases p402_3 (m.d 1 2) (by simp) with h464 | h464
                          · linarith only [h263, h464, hlam]
                          · rcases p402_3 (m.d 1 3) (by simp) with h466 | h466
                            · linarith only [h340, h466, hlam]
                            · rcases p402_3 (m.d 1 4) (by simp) with h468 | h468
                              · rcases p402_3 (m.d 1 5) (by simp) with h469 | h469
                                · rcases h2bigk with h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h398, h4, h7, h9, hlam, p470_2]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    rcases p470_3 (m.d 0 2) (by simp) with h473 | h473
                                    · rcases p470_3 (m.d 1 2) (by simp) with h474 | h474
                                      · linarith only [h0, h474, hlam]
                                      · rcases p470_3 (m.d 2 3) (by simp) with h476 | h476
                                        · linarith only [h476, hlam, p470_0]
                                        · rcases p470_3 (m.d 2 4) (by simp) with h478 | h478
                                          · linarith only [h478, h5, hlam]
                                          · linarith only [h396, h478, hlam]
                                    · linarith only [h473, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h0, h261, h395, hc01, hlam, hphi, ht0b, ht45, ht5b, p470_1, u4ehi4]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h0, h263, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p402_1, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h0, hlam, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h9, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h261, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h263, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h4, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h0, h398, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h396, hlam, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h398, hlam, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h5, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    rcases p470_3 (m.d 0 2) (by simp) with h495 | h495
                                    · rcases p470_3 (m.d 1 2) (by simp) with h496 | h496
                                      · linarith only [h496, hlam, p470_0]
                                      · rcases p470_3 (m.d 2 3) (by simp) with h498 | h498
                                        · linarith only [h396, h498, hlam]
                                        · linarith only [h498, h9, hlam]
                                    · linarith only [h0, h495, hlam]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h9, hc12, hc24, hlam, hphi, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h0, h263, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p402_1, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h6, hlam, p470_0]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    rcases p470_3 (m.d 0 2) (by simp) with h506 | h506
                                    · rcases p470_3 (m.d 1 2) (by simp) with h507 | h507
                                      · linarith only [h507, hlam, p470_0]
                                      · rcases p470_3 (m.d 2 3) (by simp) with h509 | h509
                                        · linarith only [h398, h509, hlam]
                                        · linarith only [h509, h9, hlam]
                                    · linarith only [h0, h506, hlam]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h9, hc12, hc25, hlam, hphi, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [h400, hlam, p470_1]
                                  · have p470_0 := h470c.1
                                    have p470_1 := h470c.2.1
                                    have p470_2 := h470c.2.2.1
                                    have p470_3 := h470c.2.2.2
                                    linarith only [hlam, p470_0]
                                · linarith only [h340, h469, hlam]
                              · linarith only [h265, h468, hlam]
                        · linarith only [h1, h463, hlam]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [h395, hlam, p402_0]
                      · have p402_0 := h402c.1
                        have p402_1 := h402c.2.1
                        have p402_2 := h402c.2.2.1
                        have p402_3 := h402c.2.2.2
                        linarith only [hlam, p402_0]
                    · linarith only [h265, h395, h401, hlam]
                  · linarith only [h2, h395, h400, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h523 | h523
              · rcases m.htr 2 3 5 (by decide) (by decide) with h524 | h524
                · rcases m.htr 2 4 5 (by decide) (by decide) with h525 | h525
                  · linarith only [h0, h395, h4, h523, h525, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h527 | h527
                    · linarith only [h261, h525, h527, hc12, hc34, hlam, hphi, ht23]
                    · rcases h1bigk with h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [hlam, p529_0]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h0, h265, h5, h523, h525, h8, h9, hlam, p529_2]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h0, h265, h5, h523, h525, h8, hlam, p529_2]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        rcases p529_3 (m.d 0 1) (by simp) with h533 | h533
                        · rcases p529_3 (m.d 1 2) (by simp) with h534 | h534
                          · linarith only [h0, h534, hlam]
                          · rcases p529_3 (m.d 1 3) (by simp) with h536 | h536
                            · linarith only [h1, h536, hlam]
                            · rcases p529_3 (m.d 1 4) (by simp) with h538 | h538
                              · linarith only [h538, hlam, p529_0]
                              · rcases p529_3 (m.d 1 5) (by simp) with h540 | h540
                                · linarith only [h3, h540, hlam]
                                · linarith only [h395, h540, hlam]
                        · linarith only [h533, hlam, p529_0]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        rcases p529_3 (m.d 0 1) (by simp) with h544 | h544
                        · rcases p529_3 (m.d 1 2) (by simp) with h545 | h545
                          · linarith only [h0, h545, hlam]
                          · rcases p529_3 (m.d 1 3) (by simp) with h547 | h547
                            · linarith only [h1, h547, hlam]
                            · rcases p529_3 (m.d 1 4) (by simp) with h549 | h549
                              · linarith only [h2, h549, hlam]
                              · rcases p529_3 (m.d 1 5) (by simp) with h551 | h551
                                · linarith only [h551, hlam, p529_0]
                                · rcases h2bigk with h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h265, h5, h523, h525, h8, h9, hlam, p553_2]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h0, h340, h524, hc01, hlam, hphi, ht0b, ht5b, p553_1, u5ehi1]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    rcases p553_3 (m.d 0 2) (by simp) with h557 | h557
                                    · rcases p553_3 (m.d 1 2) (by simp) with h558 | h558
                                      · linarith only [h0, h558, hlam]
                                      · rcases p553_3 (m.d 2 3) (by simp) with h560 | h560
                                        · linarith only [h4, h560, hlam]
                                        · linarith only [h523, h560, hlam]
                                    · linarith only [h557, hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    rcases p553_3 (m.d 0 2) (by simp) with h564 | h564
                                    · rcases p553_3 (m.d 1 2) (by simp) with h565 | h565
                                      · linarith only [h0, h565, hlam]
                                      · rcases p553_3 (m.d 2 3) (by simp) with h567 | h567
                                        · linarith only [h4, h567, hlam]
                                        · linarith only [h524, h567, hlam]
                                    · linarith only [h564, hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h0, hlam, p553_1]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h9, hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h261, hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h263, hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h4, hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    rcases p553_3 (m.d 0 2) (by simp) with h577 | h577
                                    · rcases p553_3 (m.d 1 2) (by simp) with h578 | h578
                                      · linarith only [h578, hlam, p553_0]
                                      · rcases p553_3 (m.d 2 3) (by simp) with h580 | h580
                                        · rcases p553_3 (m.d 2 4) (by simp) with h581 | h581
                                          · linarith only [h523, h581, hlam]
                                          · linarith only [h261, h581, hlam]
                                        · linarith only [h580, hlam, p553_0]
                                    · linarith only [h0, h577, hlam]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h265, h523, h9, hc12, hc23, hlam, hphi, p553_1]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p553_1, u5ehi2]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h5, hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h0, h5, h525, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p553_1]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h523, hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h525, hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h6, hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    rcases p553_3 (m.d 0 2) (by simp) with h595 | h595
                                    · rcases p553_3 (m.d 1 2) (by simp) with h596 | h596
                                      · linarith only [h596, hlam, p553_0]
                                      · rcases p553_3 (m.d 2 3) (by simp) with h598 | h598
                                        · rcases p553_3 (m.d 2 4) (by simp) with h599 | h599
                                          · linarith only [h525, h599, hlam]
                                          · linarith only [h261, h599, hlam]
                                        · linarith only [h598, h9, hlam]
                                    · linarith only [h0, h595, hlam]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h524, hlam, p553_0]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [h0, h265, h523, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p553_1]
                                  · have p553_0 := h553c.1
                                    have p553_1 := h553c.2.1
                                    have p553_2 := h553c.2.2.1
                                    have p553_3 := h553c.2.2.2
                                    linarith only [hlam, p553_0]
                        · linarith only [h544, hlam, p529_0]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h0, hlam, p529_0]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [hlam, p529_0]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h9, hlam, p529_1]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h261, hlam, p529_1]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h263, hlam, p529_1]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h1, hlam, p529_0]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h265, h523, hc12, hc24, hlam, hphi, p529_1]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [hlam, p529_0]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h265, hlam, p529_0]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h340, hlam, p529_1]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h2, hlam, p529_0]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h0, h395, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p529_1]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h0, h395, h5, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p529_1]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [hlam, p529_0]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h395, hlam, p529_1]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h3, hlam, p529_0]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h0, h340, h4, h524, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p529_1]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h0, h340, h4, h524, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p529_1]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [h0, h340, h4, h524, hc01, hlam, hphi, ht0b, ht45, ht5b, p529_1, u4ehi1]
                      · have p529_0 := h529c.1
                        have p529_1 := h529c.2.1
                        have p529_2 := h529c.2.2.1
                        have p529_3 := h529c.2.2.2
                        linarith only [hlam, p529_0]
                · linarith only [h4, h523, h524, h7, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h629 | h629
                · linarith only [h340, h523, h629, h9, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h631 | h631
                  · linarith only [h0, h395, h5, h631, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h633 | h633
                    · linarith only [h523, h631, h633, h9, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h523, h633, h9, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
