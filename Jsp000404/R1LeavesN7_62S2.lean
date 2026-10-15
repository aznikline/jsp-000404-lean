import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3038000 in
set_option maxHeartbeats 3038000 in
theorem r1l7_11_13_25_L_R_L_I_M_IR_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
      · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h0, h14, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h0, h11, h13, h14, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h13, h17, h4, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                      · linarith only [h0, h10, h19, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · linarith only [h0, h10, h12, h13, h19, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                    · linarith only [h0, h23, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h0, h11, h22, h23, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h0, h10, h12, h22, h26, h4, h5, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                      · linarith only [h10, h12, h28, hlam]
                      · rcases h3bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, h10, h22, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h10, h12, h22, h5, h7, hlam, p30_2]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          rcases p30_3 (m.d 0 3) (by simp) with h34 | h34
                          · rcases p30_3 (m.d 1 3) (by simp) with h35 | h35
                            · linarith only [h1, h35, hlam]
                            · linarith only [h10, h35, hlam]
                          · linarith only [h34, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          rcases p30_3 (m.d 0 3) (by simp) with h39 | h39
                          · rcases p30_3 (m.d 1 3) (by simp) with h40 | h40
                            · linarith only [h1, h40, hlam]
                            · linarith only [h11, h40, hlam]
                          · linarith only [h39, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h1, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          rcases p30_3 (m.d 0 3) (by simp) with h46 | h46
                          · rcases p30_3 (m.d 1 3) (by simp) with h47 | h47
                            · rcases p30_3 (m.d 2 3) (by simp) with h48 | h48
                              · linarith only [h48, h8, hlam]
                              · rcases p30_3 (m.d 3 4) (by simp) with h50 | h50
                                · linarith only [h10, h50, hlam]
                                · linarith only [h22, h50, hlam]
                            · linarith only [h47, h8, hlam]
                          · linarith only [h4, h46, hlam]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h1, h22, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, h22, h28, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h4, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h8, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h22, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h26, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h5, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h10, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, h10, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h28, hlam, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h6, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h11, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, h11, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, h11, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
                · linarith only [h0, h10, h11, h4, h6, h72, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
                    · linarith only [h10, h11, h75, hc23, hlam, hphi, ht12, u1ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                      · linarith only [h72, h77, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                      · rcases h3bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          rcases p79_3 (m.d 0 3) (by simp) with h81 | h81
                          · rcases p79_3 (m.d 1 3) (by simp) with h82 | h82
                            · linarith only [h1, h82, hlam]
                            · rcases p79_3 (m.d 2 3) (by simp) with h84 | h84
                              · linarith only [h4, h84, hlam]
                              · rcases p79_3 (m.d 3 4) (by simp) with h86 | h86
                                · linarith only [h5, h86, hlam]
                                · rcases p79_3 (m.d 3 5) (by simp) with h88 | h88
                                  · linarith only [h6, h88, hlam]
                                  · linarith only [h11, h88, hlam]
                          · linarith only [h1, h81, hlam]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          rcases p79_3 (m.d 0 3) (by simp) with h92 | h92
                          · rcases p79_3 (m.d 1 3) (by simp) with h93 | h93
                            · linarith only [h1, h93, hlam]
                            · linarith only [h8, h93, hlam]
                          · linarith only [h4, h92, hlam]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h11, h5, h7, h74, h77, h8, hlam, p79_2]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h0, h10, h11, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p79_1, u1ehi3]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h1, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h11, h74, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h0, h11, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h11, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h4, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h8, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h75, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h5, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h10, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h74, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h77, hlam, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h6, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p79_1, u1ehi2]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h0, h4, h6, h74, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          rcases p79_3 (m.d 0 3) (by simp) with h117 | h117
                          · rcases p79_3 (m.d 1 3) (by simp) with h118 | h118
                            · linarith only [h11, h118, hlam]
                            · linarith only [h10, h118, hlam]
                          · linarith only [h117, h5, hlam]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [hlam, p79_0]
                  · linarith only [h10, h11, h74, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h124 | h124
              · linarith only [h0, h10, h124, h4, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h126 | h126
                · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                  · linarith only [h10, h127, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h129 | h129
                    · linarith only [h0, h10, h129, h4, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
                      · rcases h3bigk with h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          rcases p132_3 (m.d 0 3) (by simp) with h134 | h134
                          · rcases p132_3 (m.d 1 3) (by simp) with h135 | h135
                            · linarith only [h1, h135, hlam]
                            · rcases p132_3 (m.d 2 3) (by simp) with h137 | h137
                              · linarith only [h137, h4, hlam]
                              · rcases p132_3 (m.d 3 4) (by simp) with h139 | h139
                                · linarith only [h139, h5, hlam]
                                · linarith only [h10, h139, hlam]
                          · linarith only [h1, h134, hlam]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          rcases p132_3 (m.d 0 3) (by simp) with h143 | h143
                          · rcases p132_3 (m.d 1 3) (by simp) with h144 | h144
                            · linarith only [h1, h144, hlam]
                            · linarith only [h144, h8, hlam]
                          · linarith only [h143, h4, hlam]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h124, h131, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p132_1, u1ehi2]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h124, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p132_1, u1ehi2]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h1, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h124, h131, hc23, hc34, hlam, hphi, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h10, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h124, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h4, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h8, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h127, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h129, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h5, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p132_1, u1ehi2]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          rcases p132_3 (m.d 0 3) (by simp) with h162 | h162
                          · rcases p132_3 (m.d 1 3) (by simp) with h163 | h163
                            · linarith only [h10, h163, hlam]
                            · linarith only [h163, h8, hlam]
                          · linarith only [h162, h4, hlam]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h4, h5, hc01, hlam, hphi, ht0b, ht5b, p132_1, u5ehi3]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h6, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p132_1, u1ehi2]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          rcases p132_3 (m.d 0 3) (by simp) with h171 | h171
                          · rcases p132_3 (m.d 1 3) (by simp) with h172 | h172
                            · linarith only [h124, h172, hlam]
                            · linarith only [h172, h8, hlam]
                          · linarith only [h171, h4, hlam]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h131, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                      · linarith only [h0, h10, h131, h4, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h179 | h179
                  · linarith only [h10, h179, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h181 | h181
                    · linarith only [h0, h10, h181, h4, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h183 | h183
                      · linarith only [h0, h10, h126, h183, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                      · linarith only [h0, h10, h183, h4, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h186 | h186
            · rcases m.htr 1 3 5 (by decide) (by decide) with h187 | h187
              · linarith only [h187, h8, h9, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                · linarith only [h0, h186, h187, h189, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                    · linarith only [h187, h192, h8, h9, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h191, h192, h4, h6, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h186, h187, h191, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h196 | h196
              · linarith only [h0, h186, h196, h4, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h198 | h198
                · rcases m.htr 2 3 4 (by decide) (by decide) with h199 | h199
                  · linarith only [h186, h199, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h201 | h201
                    · linarith only [h196, h201, h8, hc12, hlam, hphi, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h203 | h203
                      · rcases h3bigk with h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          rcases p204_3 (m.d 0 3) (by simp) with h206 | h206
                          · rcases p204_3 (m.d 1 3) (by simp) with h207 | h207
                            · linarith only [h1, h207, hlam]
                            · rcases p204_3 (m.d 2 3) (by simp) with h209 | h209
                              · linarith only [h209, h4, hlam]
                              · rcases p204_3 (m.d 3 4) (by simp) with h211 | h211
                                · linarith only [h211, h5, hlam]
                                · linarith only [h186, h211, hlam]
                          · linarith only [h1, h206, hlam]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h201, h203, h5, h8, h9, hlam, p204_2]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h0, h201, h203, h4, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p204_1, u1ehi2]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h0, h201, h4, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p204_1, u1ehi2]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h1, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h201, h203, h8, h9, hc23, hc34, hlam, hphi, p204_1]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h186, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h196, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h4, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h8, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h199, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h201, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h5, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h0, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p204_1, u1ehi2]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          rcases p204_3 (m.d 0 3) (by simp) with h230 | h230
                          · rcases p204_3 (m.d 1 3) (by simp) with h231 | h231
                            · linarith only [h186, h231, hlam]
                            · linarith only [h231, h8, hlam]
                          · linarith only [h230, h4, hlam]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h0, h201, h4, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p204_1]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h6, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p204_1, u1ehi2]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          rcases p204_3 (m.d 0 3) (by simp) with h239 | h239
                          · rcases p204_3 (m.d 1 3) (by simp) with h240 | h240
                            · linarith only [h196, h240, hlam]
                            · linarith only [h240, h8, hlam]
                          · linarith only [h239, h4, hlam]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h203, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hlam, p204_0]
                      · linarith only [h186, h198, h203, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                  · linarith only [h186, h247, h8, hc12, hlam, hphi, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h249 | h249
                    · linarith only [h249, h8, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h251 | h251
                      · linarith only [h186, h198, h251, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                      · linarith only [h0, h186, h251, h4, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
          · linarith only [h0, h254, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h256 | h256
            · rcases m.htr 1 3 5 (by decide) (by decide) with h257 | h257
              · rcases m.htr 1 4 5 (by decide) (by decide) with h258 | h258
                · rcases m.htr 2 3 4 (by decide) (by decide) with h259 | h259
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h261 | h261
                      · linarith only [h1, h256, h261, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases h3bigk with h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h0, h256, h258, h261, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p263_1]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p263_1, u1ehi1]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          rcases p263_3 (m.d 0 3) (by simp) with h267 | h267
                          · rcases p263_3 (m.d 1 3) (by simp) with h268 | h268
                            · linarith only [h1, h268, hlam]
                            · linarith only [h256, h268, hlam]
                          · linarith only [h267, hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          rcases p263_3 (m.d 0 3) (by simp) with h272 | h272
                          · rcases p263_3 (m.d 1 3) (by simp) with h273 | h273
                            · linarith only [h1, h273, hlam]
                            · linarith only [h257, h273, hlam]
                          · linarith only [h272, hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h1, hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h8, hlam, p263_1]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          rcases p263_3 (m.d 0 3) (by simp) with h280 | h280
                          · rcases p263_3 (m.d 1 3) (by simp) with h281 | h281
                            · rcases p263_3 (m.d 2 3) (by simp) with h282 | h282
                              · rcases p263_3 (m.d 3 4) (by simp) with h283 | h283
                                · linarith only [h283, hlam, p263_0]
                                · rcases p263_3 (m.d 3 5) (by simp) with h285 | h285
                                  · linarith only [h257, h285, hlam]
                                  · linarith only [h261, h285, hlam]
                              · linarith only [h259, h282, hlam]
                            · linarith only [h281, hlam, p263_0]
                          · linarith only [h280, h5, hlam]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p263_1, u5ehi3]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h4, hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [hc23, hlam, hphi, ht12, p263_1, u1ehi2]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          rcases p263_3 (m.d 0 3) (by simp) with h295 | h295
                          · rcases p263_3 (m.d 1 3) (by simp) with h296 | h296
                            · linarith only [h296, h8, hlam]
                            · linarith only [h256, h296, hlam]
                          · linarith only [h295, h5, hlam]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p263_1, u5ehi3]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h5, hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h256, hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h259, hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h261, hlam, p263_1]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h6, hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h257, hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h260, hlam, p263_0]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [h1, h257, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p263_1]
                        · have p263_0 := h263c.1
                          have p263_1 := h263c.2.1
                          have p263_2 := h263c.2.2.1
                          have p263_3 := h263c.2.2.2
                          linarith only [hlam, p263_0]
                    · linarith only [h257, h260, h8, hlam]
                  · linarith only [h257, h259, h5, h8, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h313 | h313
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h314 | h314
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h315 | h315
                      · linarith only [h256, h258, h315, hc13, hlam, hphi, u1ehi3]
                      · rcases h3bigk with h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h0, h257, h4, hc01, hlam, hphi, ht0b, ht5b, p317_1, u5ehi3]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p317_1, u1ehi1]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          rcases p317_3 (m.d 0 3) (by simp) with h321 | h321
                          · rcases p317_3 (m.d 1 3) (by simp) with h322 | h322
                            · linarith only [h1, h322, hlam]
                            · linarith only [h256, h322, hlam]
                          · linarith only [h321, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          rcases p317_3 (m.d 0 3) (by simp) with h326 | h326
                          · rcases p317_3 (m.d 1 3) (by simp) with h327 | h327
                            · linarith only [h1, h327, hlam]
                            · linarith only [h257, h327, hlam]
                          · linarith only [h326, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h1, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h8, hlam, p317_1]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          rcases p317_3 (m.d 0 3) (by simp) with h334 | h334
                          · rcases p317_3 (m.d 1 3) (by simp) with h335 | h335
                            · rcases p317_3 (m.d 2 3) (by simp) with h336 | h336
                              · rcases p317_3 (m.d 3 4) (by simp) with h337 | h337
                                · linarith only [h337, hlam, p317_0]
                                · rcases p317_3 (m.d 3 5) (by simp) with h339 | h339
                                  · linarith only [h257, h339, hlam]
                                  · linarith only [h315, h339, hlam]
                              · linarith only [h313, h336, hlam]
                            · linarith only [h335, hlam, p317_0]
                          · linarith only [h334, h5, hlam]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p317_1, u5ehi3]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h4, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [hc23, hlam, hphi, ht12, p317_1, u1ehi2]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          rcases p317_3 (m.d 0 3) (by simp) with h349 | h349
                          · rcases p317_3 (m.d 1 3) (by simp) with h350 | h350
                            · linarith only [h350, h8, hlam]
                            · linarith only [h256, h350, hlam]
                          · linarith only [h349, h5, hlam]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p317_1, u5ehi3]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h5, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h256, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h313, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h315, hlam, p317_1]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h6, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h257, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h314, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h1, h257, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p317_1]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [hlam, p317_0]
                    · linarith only [h257, h314, h8, hlam]
                  · linarith only [h0, h257, h313, h4, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h367 | h367
                · linarith only [h0, h256, h257, h367, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h369 | h369
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h370 | h370
                    · linarith only [h257, h370, hc23, hlam, hphi, ht12, u1ehi2]
                    · linarith only [h0, h370, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                  · linarith only [h0, h256, h257, h369, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
              · linarith only [h0, h256, h374, h4, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h376 | h376
                · rcases m.htr 2 3 4 (by decide) (by decide) with h377 | h377
                  · linarith only [h256, h377, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h0, h377, h4, h5, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
                  · linarith only [h0, h256, h380, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                  · linarith only [h380, h8, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h383 | h383
        · rcases m.htr 1 2 5 (by decide) (by decide) with h384 | h384
          · rcases m.htr 1 3 4 (by decide) (by decide) with h385 | h385
            · rcases m.htr 1 3 5 (by decide) (by decide) with h386 | h386
              · rcases m.htr 1 4 5 (by decide) (by decide) with h387 | h387
                · linarith only [h2, h387, h7, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h389 | h389
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h390 | h390
                    · linarith only [h0, h383, h390, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h1, h386, h389, h390, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h393 | h393
                    · linarith only [h2, h385, h389, h393, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h395 | h395
                      · linarith only [h0, h383, h385, h395, h7, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h3bigk with h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h0, h385, h389, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p397_1]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          rcases p397_3 (m.d 0 3) (by simp) with h400 | h400
                          · rcases p397_3 (m.d 1 3) (by simp) with h401 | h401
                            · linarith only [h1, h401, hlam]
                            · linarith only [h383, h401, hlam]
                          · linarith only [h4, h400, hlam]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          rcases p397_3 (m.d 0 3) (by simp) with h405 | h405
                          · rcases p397_3 (m.d 1 3) (by simp) with h406 | h406
                            · linarith only [h1, h406, hlam]
                            · linarith only [h385, h406, hlam]
                          · linarith only [h405, hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          rcases p397_3 (m.d 0 3) (by simp) with h410 | h410
                          · rcases p397_3 (m.d 1 3) (by simp) with h411 | h411
                            · linarith only [h1, h411, hlam]
                            · linarith only [h386, h411, hlam]
                          · linarith only [h410, hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h1, hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          rcases p397_3 (m.d 0 3) (by simp) with h417 | h417
                          · rcases p397_3 (m.d 1 3) (by simp) with h418 | h418
                            · rcases p397_3 (m.d 2 3) (by simp) with h419 | h419
                              · linarith only [h383, h419, hlam]
                              · rcases p397_3 (m.d 3 4) (by simp) with h421 | h421
                                · linarith only [h385, h421, hlam]
                                · linarith only [h389, h421, hlam]
                            · linarith only [h383, h418, hlam]
                          · linarith only [h4, h417, hlam]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h1, h389, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p397_1]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h0, h383, h389, h395, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p397_1]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h4, hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h383, hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h389, hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h393, hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h5, hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h385, hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h5, h7, hc23, hc45, hlam, hphi, ht34, p397_1]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h395, hlam, p397_1]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h6, hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h386, hlam, p397_0]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h0, h383, h386, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p397_1]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [h0, h383, h386, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p397_1]
                        · have p397_0 := h397c.1
                          have p397_1 := h397c.2.1
                          have p397_2 := h397c.2.2.1
                          have p397_3 := h397c.2.2.2
                          linarith only [hlam, p397_0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h443 | h443
                · linarith only [h2, h443, h7, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h445 | h445
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h446 | h446
                    · linarith only [h385, h386, h446, hc23, hlam, hphi, ht12, u1ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h448 | h448
                      · linarith only [h385, h386, h448, h6, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                      · rcases h3bigk with h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          rcases p450_3 (m.d 0 3) (by simp) with h452 | h452
                          · rcases p450_3 (m.d 1 3) (by simp) with h453 | h453
                            · linarith only [h1, h453, hlam]
                            · rcases p450_3 (m.d 2 3) (by simp) with h455 | h455
                              · linarith only [h4, h455, hlam]
                              · rcases p450_3 (m.d 3 4) (by simp) with h457 | h457
                                · linarith only [h457, h5, hlam]
                                · rcases p450_3 (m.d 3 5) (by simp) with h459 | h459
                                  · linarith only [h459, h6, hlam]
                                  · linarith only [h386, h459, hlam]
                          · linarith only [h1, h452, hlam]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          rcases p450_3 (m.d 0 3) (by simp) with h463 | h463
                          · rcases p450_3 (m.d 1 3) (by simp) with h464 | h464
                            · linarith only [h1, h464, hlam]
                            · linarith only [h383, h464, hlam]
                          · linarith only [h4, h463, hlam]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h383, h386, h445, h6, hlam, p450_2]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h385, h386, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p450_1, u1ehi3]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h1, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h386, h445, h6, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h0, h386, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h386, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h4, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h383, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h0, h383, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h446, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h5, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h385, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h445, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h448, hlam, p450_1]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h6, hlam, p450_0]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p450_1, u1ehi2]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [h0, h4, h445, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          rcases p450_3 (m.d 0 3) (by simp) with h488 | h488
                          · rcases p450_3 (m.d 1 3) (by simp) with h489 | h489
                            · linarith only [h386, h489, hlam]
                            · linarith only [h385, h489, hlam]
                          · linarith only [h488, h5, hlam]
                        · have p450_0 := h450c.1
                          have p450_1 := h450c.2.1
                          have p450_2 := h450c.2.2.1
                          have p450_3 := h450c.2.2.2
                          linarith only [hlam, p450_0]
                  · linarith only [h0, h385, h386, h4, h445, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h385, h5, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h496 | h496
            · rcases m.htr 1 3 5 (by decide) (by decide) with h497 | h497
              · linarith only [h383, h384, h497, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h499 | h499
                · linarith only [h2, h499, h7, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h501 | h501
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h502 | h502
                    · linarith only [h383, h384, h496, h497, h502, hc25, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h0, h383, h384, h4, h501, h502, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h4, h496, h497, h501, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h496, h5, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h507 | h507
          · linarith only [h0, h383, h4, h507, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h509 | h509
            · rcases m.htr 1 3 5 (by decide) (by decide) with h510 | h510
              · rcases m.htr 1 4 5 (by decide) (by decide) with h511 | h511
                · linarith only [h2, h511, h7, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h513 | h513
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h514 | h514
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h515 | h515
                      · linarith only [h2, h509, h515, h7, hc13, hlam, hphi, u1ehi3]
                      · rcases h3bigk with h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h0, h4, h510, hc01, hlam, hphi, ht0b, ht5b, p517_1, u5ehi3]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h0, h383, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p517_1, u1ehi1]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          rcases p517_3 (m.d 0 3) (by simp) with h521 | h521
                          · rcases p517_3 (m.d 1 3) (by simp) with h522 | h522
                            · linarith only [h1, h522, hlam]
                            · linarith only [h509, h522, hlam]
                          · linarith only [h521, hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          rcases p517_3 (m.d 0 3) (by simp) with h526 | h526
                          · rcases p517_3 (m.d 1 3) (by simp) with h527 | h527
                            · linarith only [h1, h527, hlam]
                            · linarith only [h510, h527, hlam]
                          · linarith only [h526, hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h1, hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h383, hlam, p517_1]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          rcases p517_3 (m.d 0 3) (by simp) with h534 | h534
                          · rcases p517_3 (m.d 1 3) (by simp) with h535 | h535
                            · rcases p517_3 (m.d 2 3) (by simp) with h536 | h536
                              · rcases p517_3 (m.d 3 4) (by simp) with h537 | h537
                                · linarith only [h537, hlam, p517_0]
                                · rcases p517_3 (m.d 3 5) (by simp) with h539 | h539
                                  · linarith only [h510, h539, hlam]
                                  · linarith only [h515, h539, hlam]
                              · linarith only [h513, h536, hlam]
                            · linarith only [h535, hlam, p517_0]
                          · linarith only [h5, h534, hlam]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h0, h383, h4, hc01, hlam, hphi, ht0b, ht5b, p517_1, u5ehi3]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h4, hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p517_1, u1ehi2]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          rcases p517_3 (m.d 0 3) (by simp) with h549 | h549
                          · rcases p517_3 (m.d 1 3) (by simp) with h550 | h550
                            · linarith only [h383, h550, hlam]
                            · linarith only [h509, h550, hlam]
                          · linarith only [h5, h549, hlam]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p517_1, u5ehi3]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h5, hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h509, hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h513, hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h515, hlam, p517_1]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h6, hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h510, hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h514, hlam, p517_0]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [h1, h510, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p517_1]
                        · have p517_0 := h517c.1
                          have p517_1 := h517c.2.1
                          have p517_2 := h517c.2.2.1
                          have p517_3 := h517c.2.2.2
                          linarith only [hlam, p517_0]
                    · linarith only [h383, h510, h514, hlam]
                  · linarith only [h0, h383, h4, h5, h510, h513, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h567 | h567
                · linarith only [h510, h567, h6, h7, hc14, hlam, hphi, u1ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h569 | h569
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h570 | h570
                    · linarith only [h383, h510, h570, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h383, h570, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h383, h509, h569, hc13, hlam, hphi, u1ehi1]
            · linarith only [h5, h509, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h575 | h575
      · linarith only [h5, h575, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h577 | h577
        · rcases m.htr 1 2 5 (by decide) (by decide) with h578 | h578
          · rcases m.htr 1 3 4 (by decide) (by decide) with h579 | h579
            · rcases m.htr 1 3 5 (by decide) (by decide) with h580 | h580
              · linarith only [h1, h580, h6, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h582 | h582
                · linarith only [h2, h575, h582, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h584 | h584
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h585 | h585
                    · linarith only [h1, h577, h585, h6, hc12, hlam, hphi, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h587 | h587
                      · linarith only [h0, h2, h575, h578, h584, h585, h587, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                      · rcases h3bigk with h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h577, h584, h6, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h584, h587, h6, hc34, hc45, hlam, hphi, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h587, h6, hc34, hc45, hlam, hphi, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h6, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h1, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h1, h584, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h1, h587, h6, hc34, hc45, hlam, hphi, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h580, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h4, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h577, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h4, h587, h6, hc34, hc45, hlam, hphi, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h585, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h5, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h579, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h584, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h587, hlam, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h1, h587, hc45, hlam, hphi, ht12, ht23, ht34, p589_1, u1ehi2]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h579, h587, hc45, hlam, hphi, ht12, ht23, ht34, p589_1, u1ehi3]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h584, h587, hc34, hc45, hlam, hphi, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          rcases p589_3 (m.d 0 3) (by simp) with h613 | h613
                          · linarith only [h6, h613, hlam]
                          · linarith only [h5, h613, hlam]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [hlam, p589_0]
                  · linarith only [h5, h584, h6, hc23, hc35, hlam, hphi]
            · linarith only [h5, h579, h6, hc13, hc35, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h619 | h619
            · rcases m.htr 1 3 5 (by decide) (by decide) with h620 | h620
              · linarith only [h1, h6, h620, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h622 | h622
                · linarith only [h2, h575, h622, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h624 | h624
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h625 | h625
                    · linarith only [h577, h578, h6, h625, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h627 | h627
                      · linarith only [h577, h578, h624, h625, h627, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h577, h578, h624, h625, h627, hc34, hc45, hlam, hphi]
                  · linarith only [h5, h6, h624, hc23, hc35, hlam, hphi]
            · linarith only [h5, h6, h619, hc13, hc35, hlam, hphi]
        · linarith only [h4, h577, h6, hc35, hlam, hphi, ht12, ht23, u1ehi1]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h633 | h633
    · rcases m.htr 0 4 5 (by decide) (by decide) with h634 | h634
      · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
        · rcases m.htr 1 2 5 (by decide) (by decide) with h636 | h636
          · rcases m.htr 1 3 4 (by decide) (by decide) with h637 | h637
            · linarith only [h5, h633, h637, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h639 | h639
              · rcases m.htr 1 4 5 (by decide) (by decide) with h640 | h640
                · rcases m.htr 2 3 4 (by decide) (by decide) with h641 | h641
                  · linarith only [h0, h1, h5, h635, h639, h641, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h643 | h643
                    · linarith only [h0, h635, h643, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h1, h5, h639, h643, hc23, hc34, hlam, hphi]
                · linarith only [h634, h637, h639, h640, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h5, h633, h639, hc34, hlam, hphi, ht12, ht23, u1ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h648 | h648
            · linarith only [h3, h5, h633, h635, h636, h648, hc05, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h650 | h650
              · linarith only [h635, h636, h650, hlam]
              · linarith only [h5, h633, h650, hc34, hlam, hphi, ht12, ht23, u1ehi2]
        · linarith only [h4, h5, h635, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · linarith only [h5, h633, h634, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h655 | h655
      · rcases m.htr 1 2 3 (by decide) (by decide) with h656 | h656
        · rcases m.htr 1 2 5 (by decide) (by decide) with h657 | h657
          · rcases m.htr 1 3 4 (by decide) (by decide) with h658 | h658
            · linarith only [h1, h5, h655, h658, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h660 | h660
              · linarith only [h1, h633, h660, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h662 | h662
                · rcases m.htr 2 3 4 (by decide) (by decide) with h663 | h663
                  · linarith only [h1, h5, h656, h663, hc12, hlam, hphi, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h665 | h665
                    · linarith only [h1, h633, h656, h665, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h667 | h667
                      · rcases h3bigk with h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h633, h667, hc34, hlam, hphi, ht12, ht23, p668_1, u1ehi2]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h633, h667, hc23, hc34, hlam, hphi, p668_1]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h5, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h633, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h1, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h1, h633, h667, hc23, hc34, hlam, hphi, p668_1]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h658, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h660, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h4, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h656, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h663, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h665, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h1, hc34, hlam, hphi, ht12, ht23, p668_1, u1ehi2]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p668_1, u1ehi2]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          rcases p668_3 (m.d 0 3) (by simp) with h686 | h686
                          · linarith only [h5, h686, hlam]
                          · linarith only [h4, h686, hlam]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h1, h633, hc34, hlam, hphi, ht12, ht23, p668_1, u1ehi2]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht12, ht23, p668_1, u1ehi2]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p668_1, u1ehi2]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          rcases p668_3 (m.d 0 3) (by simp) with h693 | h693
                          · linarith only [h633, h693, hlam]
                          · linarith only [h4, h693, hlam]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h667, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hlam, p668_0]
                      · linarith only [h1, h2, h5, h662, h667, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                · linarith only [h5, h655, h662, hc34, hlam, hphi, ht12, ht23, u1ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h700 | h700
            · linarith only [h1, h5, h655, h700, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h702 | h702
              · linarith only [h1, h633, h702, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h704 | h704
                · rcases m.htr 2 3 4 (by decide) (by decide) with h705 | h705
                  · linarith only [h1, h5, h705, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h707 | h707
                    · linarith only [h656, h657, h707, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h709 | h709
                      · rcases h3bigk with h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h5, hc34, hlam, hphi, ht12, ht23, p710_1, u1ehi2]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h5, hc23, hc34, hlam, hphi, p710_1]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h5, hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h633, hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h1, hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h1, h633, h709, hc23, hc34, hlam, hphi, p710_1]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h700, hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h702, hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h4, hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h656, hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h705, hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h707, hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h1, hc34, hlam, hphi, ht12, ht23, p710_1, u1ehi2]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p710_1, u1ehi2]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          rcases p710_3 (m.d 0 3) (by simp) with h728 | h728
                          · linarith only [h5, h728, hlam]
                          · linarith only [h4, h728, hlam]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h657, h707, hc12, hc34, hlam, hphi, ht23, p710_1]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht12, ht23, p710_1, u1ehi2]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p710_1, u1ehi2]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          rcases p710_3 (m.d 0 3) (by simp) with h735 | h735
                          · linarith only [h633, h735, hlam]
                          · linarith only [h4, h735, hlam]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [h709, hlam, p710_0]
                        · have p710_0 := h710c.1
                          have p710_1 := h710c.2.1
                          have p710_2 := h710c.2.2.1
                          have p710_3 := h710c.2.2.2
                          linarith only [hlam, p710_0]
                      · linarith only [h1, h5, h709, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · linarith only [h5, h655, h704, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · linarith only [h4, h5, h656, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h743 | h743
        · rcases m.htr 1 2 5 (by decide) (by decide) with h744 | h744
          · rcases m.htr 1 3 4 (by decide) (by decide) with h745 | h745
            · linarith only [h1, h5, h745, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h747 | h747
              · linarith only [h1, h633, h747, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h749 | h749
                · linarith only [h1, h5, h655, h749, hc14, hlam, hphi, u1ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h751 | h751
                  · linarith only [h1, h5, h743, h751, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h753 | h753
                    · linarith only [h1, h633, h743, h753, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h755 | h755
                      · linarith only [h1, h5, h655, h755, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                      · linarith only [h1, h5, h755, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h758 | h758
            · linarith only [h1, h5, h758, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h760 | h760
              · linarith only [h1, h633, h760, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h762 | h762
                · linarith only [h2, h655, h762, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h764 | h764
                  · linarith only [h1, h5, h743, h744, h764, hc25, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h766 | h766
                    · linarith only [h1, h633, h743, h744, h766, hc25, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h768 | h768
                      · linarith only [h1, h5, h655, h768, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                      · linarith only [h1, h5, h768, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · linarith only [h4, h5, h743, hc34, hlam, hphi, ht12, ht23, u1ehi1]

end R2N4
