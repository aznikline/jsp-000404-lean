import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_32S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9022000 in
set_option maxHeartbeats 9022000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                                      · linarith only [h0, h15, h18, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                      · linarith only [h0, h15, h17, h18, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                    · linarith only [h0, h12, h14, h17, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · linarith only [h0, h13, h16, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h0, h12, h15, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                                    · linarith only [h0, h14, h24, h26, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                                      · linarith only [h10, h14, h28, hc34, hlam, hphi, ht23, u2ehi3]
                                      · rcases h2bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, h25, h26, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          rcases p30_3 (m.d 0 2) (by simp) with h33 | h33
                                          · rcases p30_3 (m.d 1 2) (by simp) with h34 | h34
                                            · linarith only [h0, h34, hlam]
                                            · linarith only [h34, h9, hlam]
                                          · linarith only [h33, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          rcases p30_3 (m.d 0 2) (by simp) with h38 | h38
                                          · rcases p30_3 (m.d 1 2) (by simp) with h39 | h39
                                            · linarith only [h0, h39, hlam]
                                            · linarith only [h10, h39, hlam]
                                          · linarith only [h38, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          rcases p30_3 (m.d 0 2) (by simp) with h43 | h43
                                          · rcases p30_3 (m.d 1 2) (by simp) with h44 | h44
                                            · linarith only [h0, h44, hlam]
                                            · linarith only [h11, h44, hlam]
                                          · linarith only [h43, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, hlam, p30_1]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, h25, h26, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, h26, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h3, hlam, p30_0]
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
                                          linarith only [hc23, hlam, hphi, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, h26, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h4, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h10, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h24, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
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
                                          linarith only [h11, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h25, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hc25, hlam, hphi, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                  · linarith only [h0, h13, h25, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h0, h12, h24, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                              · linarith only [h12, h13, h70, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
                                  · linarith only [h10, h12, h13, h73, hc23, hlam, hphi, u2ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
                                    · linarith only [h10, h70, h75, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                                      · linarith only [h10, h70, h72, h77, h9, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                      · rcases h2bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p79_1, u2ehi4]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          rcases p79_3 (m.d 0 2) (by simp) with h82 | h82
                                          · rcases p79_3 (m.d 1 2) (by simp) with h83 | h83
                                            · linarith only [h0, h83, hlam]
                                            · linarith only [h83, h9, hlam]
                                          · linarith only [h82, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          rcases p79_3 (m.d 0 2) (by simp) with h87 | h87
                                          · rcases p79_3 (m.d 1 2) (by simp) with h88 | h88
                                            · linarith only [h0, h88, hlam]
                                            · linarith only [h10, h88, hlam]
                                          · linarith only [h87, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          rcases p79_3 (m.d 0 2) (by simp) with h92 | h92
                                          · rcases p79_3 (m.d 1 2) (by simp) with h93 | h93
                                            · linarith only [h0, h93, hlam]
                                            · linarith only [h11, h93, hlam]
                                          · linarith only [h92, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h0, hlam, p79_1]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h0, h72, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p79_1, u2ehi3]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h0, h73, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p79_1, u2ehi2]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h3, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h9, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [hc23, hlam, hphi, p79_1, u2ehi3]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h73, hlam, p79_1]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h4, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h10, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h72, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [hlam, p79_0]
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
                                          linarith only [h11, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [hc25, hlam, hphi, p79_1, u2ehi2]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p79_1, u2ehi3]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [hlam, p79_0]
                                · linarith only [h12, h13, h72, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                                · linarith only [h11, h118, h12, h120, hc23, hlam, hphi, u2ehi4]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h123 | h123
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
                                      · rcases h2bigk with h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h122, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p125_1]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          rcases p125_3 (m.d 0 2) (by simp) with h128 | h128
                                          · rcases p125_3 (m.d 1 2) (by simp) with h129 | h129
                                            · linarith only [h0, h129, hlam]
                                            · linarith only [h129, h9, hlam]
                                          · linarith only [h128, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          rcases p125_3 (m.d 0 2) (by simp) with h133 | h133
                                          · rcases p125_3 (m.d 1 2) (by simp) with h134 | h134
                                            · linarith only [h0, h134, hlam]
                                            · linarith only [h10, h134, hlam]
                                          · linarith only [h133, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          rcases p125_3 (m.d 0 2) (by simp) with h138 | h138
                                          · rcases p125_3 (m.d 1 2) (by simp) with h139 | h139
                                            · linarith only [h0, h139, hlam]
                                            · linarith only [h11, h139, hlam]
                                          · linarith only [h138, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, hlam, p125_1]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h122, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi4]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h120, h122, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi4]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi4]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h3, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h9, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h120, hlam, p125_1]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hc23, hlam, hphi, p125_1, u2ehi4]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h4, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h10, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hc24, hlam, hphi, p125_1, u2ehi2]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi4]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h5, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h11, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h122, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h123, hlam, p125_1]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                      · linarith only [h0, h12, h122, h124, h3, h6, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                    · linarith only [h0, h10, h119, h120, h122, h123, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                  · linarith only [h1, h118, h122, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h118, h119, h12, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h167 | h167
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                                · linarith only [h0, h12, h168, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h170 | h170
                                  · linarith only [h118, h170, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h172 | h172
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h173 | h173
                                      · rcases h2bigk with h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          rcases p174_3 (m.d 0 2) (by simp) with h177 | h177
                                          · rcases p174_3 (m.d 1 2) (by simp) with h178 | h178
                                            · linarith only [h0, h178, hlam]
                                            · linarith only [h178, h9, hlam]
                                          · linarith only [h177, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          rcases p174_3 (m.d 0 2) (by simp) with h182 | h182
                                          · rcases p174_3 (m.d 1 2) (by simp) with h183 | h183
                                            · linarith only [h0, h183, hlam]
                                            · linarith only [h10, h183, hlam]
                                          · linarith only [h182, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          rcases p174_3 (m.d 0 2) (by simp) with h187 | h187
                                          · rcases p174_3 (m.d 1 2) (by simp) with h188 | h188
                                            · linarith only [h0, h188, hlam]
                                            · linarith only [h11, h188, hlam]
                                          · linarith only [h187, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h0, hlam, p174_1]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h0, h170, h172, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h0, h170, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h3, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h9, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h168, hlam, p174_1]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h170, hlam, p174_1]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h4, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h10, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [hc24, hlam, hphi, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h0, h10, h170, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h5, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h11, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [hc25, hlam, hphi, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h172, hlam, p174_1]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [hlam, p174_0]
                                      · linarith only [h12, h173, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                    · linarith only [h0, h12, h167, h172, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                                · linarith only [h12, h214, h9, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h216 | h216
                                  · linarith only [h118, h216, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h218 | h218
                                    · linarith only [h0, h10, h167, h218, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h220 | h220
                                      · linarith only [h12, h167, h220, h9, hc34, hlam, hphi, ht23, u2ehi2]
                                      · linarith only [h12, h220, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h11, h5, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h9, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
                      · linarith only [h225, h9, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h227 | h227
                        · linarith only [h0, h227, h3, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h230 | h230
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h233 | h233
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h234 | h234
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h235 | h235
                                      · rcases h2bigk with h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          rcases p236_3 (m.d 0 2) (by simp) with h238 | h238
                                          · rcases p236_3 (m.d 1 2) (by simp) with h239 | h239
                                            · linarith only [h0, h239, hlam]
                                            · rcases p236_3 (m.d 2 3) (by simp) with h241 | h241
                                              · linarith only [h241, h3, hlam]
                                              · linarith only [h241, h9, hlam]
                                          · linarith only [h0, h238, hlam]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h0, h227, h232, h234, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h0, h227, h234, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h0, h227, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h0, hlam, p236_1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h9, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h225, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h227, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h3, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hc23, hlam, hphi, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h0, h227, h234, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h0, h227, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h4, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hc24, hlam, hphi, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h232, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h0, h227, h232, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h5, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hc25, hlam, hphi, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h233, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h234, hlam, p236_1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hlam, p236_0]
                                      · rcases h2bigk with h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [hlam, p268_0]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          rcases p268_3 (m.d 0 2) (by simp) with h270 | h270
                                          · rcases p268_3 (m.d 1 2) (by simp) with h271 | h271
                                            · linarith only [h0, h271, hlam]
                                            · rcases p268_3 (m.d 2 3) (by simp) with h273 | h273
                                              · linarith only [h273, h3, hlam]
                                              · linarith only [h273, h9, hlam]
                                          · linarith only [h0, h270, hlam]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p268_1, u2ehi1]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h0, h225, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p268_1, u2ehi1]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h0, h227, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p268_1, u2ehi1]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h0, hlam, p268_1]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [hlam, p268_0]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h9, hlam, p268_0]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h225, hlam, p268_0]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h227, hlam, p268_0]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h3, hlam, p268_0]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [hc23, hlam, hphi, p268_1, u2ehi1]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [hlam, p268_0]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h0, h225, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p268_1, u2ehi1]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h0, h227, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p268_1, u2ehi1]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h4, hlam, p268_0]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [hc24, hlam, hphi, p268_1, u2ehi1]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h232, hlam, p268_0]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [hlam, p268_0]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h0, h227, h232, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p268_1, u2ehi1]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h5, hlam, p268_0]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [hc25, hlam, hphi, p268_1, u2ehi1]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h233, hlam, p268_0]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [h234, hlam, p268_1]
                                        · have p268_0 := h268c.1
                                          have p268_1 := h268c.2.1
                                          have p268_2 := h268c.2.2.1
                                          have p268_3 := h268c.2.2.2
                                          linarith only [hlam, p268_0]
                                    · linarith only [h0, h225, h234, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h0, h233, h3, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h232, h9, hc34, hlam, hphi, ht23, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h304 | h304
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                                    · linarith only [h225, h231, h303, h305, hc23, hlam, hphi, u2ehi1]
                                    · linarith only [h0, h225, h3, h305, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h1, h230, h304, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h0, h3, h303, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h310 | h310
                              · linarith only [h229, h230, h310, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h312 | h312
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h313 | h313
                                  · linarith only [h0, h229, h230, h3, h313, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h3, h313, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h312, h9, hc34, hlam, hphi, ht23, u2ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h317 | h317
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h318 | h318
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h319 | h319
                                · linarith only [h0, h229, h3, h317, h319, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h3, h319, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h229, h317, h318, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h323 | h323
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h324 | h324
                                · linarith only [h0, h229, h3, h324, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h3, h324, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h327 | h327
                                · linarith only [h229, h327, h9, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h3, h327, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h330 | h330
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h332 | h332
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h333 | h333
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h334 | h334
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h335 | h335
                              · linarith only [h1, h333, h335, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h338 | h338
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h339 | h339
                                    · linarith only [h339, h4, h8, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h341 | h341
                                      · linarith only [h0, h330, h337, h341, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                      · rcases h2bigk with h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h0, h330, h338, h341, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p343_1]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          rcases p343_3 (m.d 0 2) (by simp) with h346 | h346
                                          · rcases p343_3 (m.d 1 2) (by simp) with h347 | h347
                                            · linarith only [h0, h347, hlam]
                                            · linarith only [h330, h347, hlam]
                                          · linarith only [h346, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          rcases p343_3 (m.d 0 2) (by simp) with h351 | h351
                                          · rcases p343_3 (m.d 1 2) (by simp) with h352 | h352
                                            · linarith only [h0, h352, hlam]
                                            · linarith only [h331, h352, hlam]
                                          · linarith only [h351, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          rcases p343_3 (m.d 0 2) (by simp) with h356 | h356
                                          · rcases p343_3 (m.d 1 2) (by simp) with h357 | h357
                                            · linarith only [h0, h357, hlam]
                                            · linarith only [h332, h357, hlam]
                                          · linarith only [h356, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h0, hlam, p343_1]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h0, h338, h339, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p343_1, u2ehi3]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p343_1, u2ehi3]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h0, h339, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p343_1, u2ehi3]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h3, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h330, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [hc23, hlam, hphi, p343_1, u2ehi3]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h0, h330, h339, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p343_1, u2ehi3]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h4, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h331, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h337, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h339, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h5, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h332, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h338, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [hc25, hlam, hphi, p343_1, u2ehi3]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [hlam, p343_0]
                                  · linarith only [h0, h330, h334, h338, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h337, h6, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h383 | h383
                              · linarith only [h333, h334, h383, h4, h8, hc35, hlam, hphi, ht23, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h385 | h385
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h386 | h386
                                  · linarith only [h0, h330, h334, h386, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h388 | h388
                                    · linarith only [h0, h330, h334, h385, h388, h4, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h390 | h390
                                      · linarith only [h390, h4, h8, hc34, hlam, hphi, ht23, u2ehi3]
                                      · rcases h2bigk with h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h0, h330, h385, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p392_1, u2ehi3]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          rcases p392_3 (m.d 0 2) (by simp) with h395 | h395
                                          · rcases p392_3 (m.d 1 2) (by simp) with h396 | h396
                                            · linarith only [h0, h396, hlam]
                                            · linarith only [h330, h396, hlam]
                                          · linarith only [h395, hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          rcases p392_3 (m.d 0 2) (by simp) with h400 | h400
                                          · rcases p392_3 (m.d 1 2) (by simp) with h401 | h401
                                            · linarith only [h0, h401, hlam]
                                            · linarith only [h331, h401, hlam]
                                          · linarith only [h400, hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          rcases p392_3 (m.d 0 2) (by simp) with h405 | h405
                                          · rcases p392_3 (m.d 1 2) (by simp) with h406 | h406
                                            · linarith only [h0, h406, hlam]
                                            · linarith only [h332, h406, hlam]
                                          · linarith only [h405, hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h0, hlam, p392_1]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h0, h385, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p392_1, u2ehi3]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p392_1, u2ehi3]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h0, h385, h386, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p392_1, u2ehi3]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h3, hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h330, hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [hc23, hlam, hphi, p392_1, u2ehi3]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h386, hlam, p392_1]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h4, hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h331, hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h385, hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h388, hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h5, hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h332, hlam, p392_0]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [hc25, hlam, hphi, p392_1, u2ehi2]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [h0, h332, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p392_1, u2ehi3]
                                        · have p392_0 := h392c.1
                                          have p392_1 := h392c.2.1
                                          have p392_2 := h392c.2.2.1
                                          have p392_3 := h392c.2.2.2
                                          linarith only [hlam, p392_0]
                                · linarith only [h385, h6, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h330, h333, h6, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h330, h332, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h330, h331, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h434 | h434
                      · linarith only [h330, h434, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h4, h434, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h437 | h437
                  · linarith only [h437, h6, h7, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h439 | h439
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h440 | h440
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h441 | h441
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h442 | h442
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h443 | h443
                            · linarith only [h1, h443, h7, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h445 | h445
                              · linarith only [h1, h4, h437, h442, h445, h7, hc35, hlam, hphi, ht23, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h447 | h447
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h448 | h448
                                  · linarith only [h0, h439, h448, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h450 | h450
                                    · linarith only [h4, h437, h450, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h452 | h452
                                      · linarith only [h1, h437, h439, h447, h452, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                      · rcases h2bigk with h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h0, h441, h447, h448, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p454_1]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          rcases p454_3 (m.d 0 2) (by simp) with h457 | h457
                                          · rcases p454_3 (m.d 1 2) (by simp) with h458 | h458
                                            · linarith only [h0, h458, hlam]
                                            · linarith only [h439, h458, hlam]
                                          · linarith only [h457, hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          rcases p454_3 (m.d 0 2) (by simp) with h462 | h462
                                          · rcases p454_3 (m.d 1 2) (by simp) with h463 | h463
                                            · linarith only [h0, h463, hlam]
                                            · linarith only [h440, h463, hlam]
                                          · linarith only [h462, hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          rcases p454_3 (m.d 0 2) (by simp) with h467 | h467
                                          · rcases p454_3 (m.d 1 2) (by simp) with h468 | h468
                                            · linarith only [h0, h468, hlam]
                                            · linarith only [h441, h468, hlam]
                                          · linarith only [h467, hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h0, hlam, p454_1]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h0, h447, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p454_1, u2ehi3]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p454_1, u2ehi3]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h0, h447, h448, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p454_1, u2ehi3]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h3, hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h439, hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [hc23, hlam, hphi, p454_1, u2ehi3]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h448, hlam, p454_1]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h4, hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h440, hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h447, hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h450, hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h5, hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h441, hlam, p454_0]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [hc25, hlam, hphi, p454_1, u2ehi2]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [h0, h441, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p454_1, u2ehi3]
                                        · have p454_0 := h454c.1
                                          have p454_1 := h454c.2.1
                                          have p454_2 := h454c.2.2.1
                                          have p454_3 := h454c.2.2.2
                                          linarith only [hlam, p454_0]
                                · linarith only [h447, h6, h7, hc23, hc35, hlam, hphi]
                          · linarith only [h442, h6, h7, hc13, hc35, hlam, hphi]
                        · linarith only [h0, h439, h441, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h439, h440, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h3, h439, h7, hc35, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h497 | h497
                · rcases m.htr 0 4 5 (by decide) (by decide) with h498 | h498
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h499 | h499
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h500 | h500
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h501 | h501
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h502 | h502
                          · linarith only [h1, h497, h502, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h504 | h504
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h505 | h505
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h506 | h506
                                · linarith only [h2, h497, h501, h506, h6, hc23, hlam, hphi, u2ehi4]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h508 | h508
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h509 | h509
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h510 | h510
                                      · rcases h2bigk with h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h0, h500, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p511_1, u2ehi3]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          rcases p511_3 (m.d 0 2) (by simp) with h514 | h514
                                          · rcases p511_3 (m.d 1 2) (by simp) with h515 | h515
                                            · linarith only [h0, h515, hlam]
                                            · linarith only [h499, h515, hlam]
                                          · linarith only [h514, hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          rcases p511_3 (m.d 0 2) (by simp) with h519 | h519
                                          · rcases p511_3 (m.d 1 2) (by simp) with h520 | h520
                                            · linarith only [h0, h520, hlam]
                                            · linarith only [h500, h520, hlam]
                                          · linarith only [h519, hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          rcases p511_3 (m.d 0 2) (by simp) with h524 | h524
                                          · rcases p511_3 (m.d 1 2) (by simp) with h525 | h525
                                            · linarith only [h0, h525, hlam]
                                            · linarith only [h501, h525, hlam]
                                          · linarith only [h524, hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h0, hlam, p511_1]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h0, h508, hc01, hc35, hlam, hphi, ht0b, ht5b, p511_1]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h0, h506, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p511_1, u2ehi2]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p511_1, u2ehi4]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h3, hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h499, hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h506, hlam, p511_1]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [hc23, hlam, hphi, p511_1, u2ehi4]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h4, hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h500, hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [hc24, hlam, hphi, p511_1, u2ehi2]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h0, h500, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p511_1, u2ehi4]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h5, hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h501, hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h508, hlam, p511_0]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [h509, hlam, p511_1]
                                        · have p511_0 := h511c.1
                                          have p511_1 := h511c.2.1
                                          have p511_2 := h511c.2.2.1
                                          have p511_3 := h511c.2.2.2
                                          linarith only [hlam, p511_0]
                                      · linarith only [h2, h497, h501, h510, h6, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                    · linarith only [h498, h509, h6, hc34, hlam, hphi, ht23, u2ehi3]
                                  · linarith only [h497, h508, h6, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h497, h498, h500, h505, h6, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h497, h504, h6, hc13, hc34, hlam, hphi]
                        · linarith only [h497, h5, h501, h6, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h499, h500, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h3, h499, h6, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h497, h498, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h558 | h558
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h559 | h559
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h560 | h560
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h561 | h561
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h562 | h562
                          · linarith only [h1, h562, h6, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h564 | h564
                            · linarith only [h1, h497, h564, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h566 | h566
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h567 | h567
                                · linarith only [h0, h4, h559, h567, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h569 | h569
                                  · linarith only [h1, h497, h559, h569, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h571 | h571
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h572 | h572
                                      · rcases h2bigk with h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h0, h559, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p573_1, u2ehi2]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          rcases p573_3 (m.d 0 2) (by simp) with h576 | h576
                                          · rcases p573_3 (m.d 1 2) (by simp) with h577 | h577
                                            · linarith only [h0, h577, hlam]
                                            · linarith only [h559, h577, hlam]
                                          · linarith only [h576, hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          rcases p573_3 (m.d 0 2) (by simp) with h581 | h581
                                          · rcases p573_3 (m.d 1 2) (by simp) with h582 | h582
                                            · linarith only [h0, h582, hlam]
                                            · linarith only [h560, h582, hlam]
                                          · linarith only [h581, hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          rcases p573_3 (m.d 0 2) (by simp) with h586 | h586
                                          · rcases p573_3 (m.d 1 2) (by simp) with h587 | h587
                                            · linarith only [h0, h587, hlam]
                                            · linarith only [h561, h587, hlam]
                                          · linarith only [h586, hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h0, hlam, p573_1]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p573_1, u2ehi2]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h0, h569, h571, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p573_1, u2ehi2]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h0, h569, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p573_1, u2ehi2]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h3, hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h559, hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h567, hlam, p573_1]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h569, hlam, p573_1]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h4, hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h560, hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [hc24, hlam, hphi, p573_1, u2ehi2]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h0, h560, h569, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p573_1, u2ehi2]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h5, hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h561, hlam, p573_0]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [hc25, hlam, hphi, p573_1, u2ehi2]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [h571, hlam, p573_1]
                                        · have p573_0 := h573c.1
                                          have p573_1 := h573c.2.1
                                          have p573_2 := h573c.2.2.1
                                          have p573_3 := h573c.2.2.2
                                          linarith only [hlam, p573_0]
                                      · linarith only [h1, h559, h572, h6, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                    · linarith only [h558, h571, h6, hc34, hlam, hphi, ht23, u2ehi3]
                              · linarith only [h558, h560, h566, h6, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h5, h559, h561, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h559, h560, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h3, h559, h6, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h617 | h617
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h618 | h618
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h619 | h619
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h620 | h620
                          · linarith only [h1, h6, h620, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h622 | h622
                            · linarith only [h1, h497, h622, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h624 | h624
                              · linarith only [h0, h1, h558, h6, h617, h618, h624, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h626 | h626
                                · linarith only [h1, h6, h617, h626, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h628 | h628
                                  · linarith only [h1, h497, h617, h628, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h630 | h630
                                    · linarith only [h1, h558, h6, h617, h630, hc24, hlam, hphi, u2ehi2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h632 | h632
                                      · linarith only [h1, h558, h6, h617, h632, hc34, hlam, hphi, ht23, u2ehi2]
                                      · linarith only [h1, h6, h617, h632, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h617, h619, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h617, h618, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h3, h6, h617, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h640 | h640
          · linarith only [h3, h640, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h642 | h642
            · linarith only [h3, h642, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h644 | h644
              · rcases m.htr 0 3 5 (by decide) (by decide) with h645 | h645
                · rcases m.htr 0 4 5 (by decide) (by decide) with h646 | h646
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h647 | h647
                    · linarith only [h0, h3, h647, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h649 | h649
                      · linarith only [h0, h640, h649, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h651 | h651
                        · linarith only [h0, h642, h651, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h653 | h653
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h654 | h654
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h655 | h655
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h656 | h656
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h657 | h657
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h658 | h658
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h659 | h659
                                      · rcases h2bigk with h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [hlam, p660_0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h642, h656, h658, hc23, hlam, hphi, p660_1, u2ehi1]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h3, hlam, p660_0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h640, hlam, p660_0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h642, hlam, p660_0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h0, hlam, p660_1]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [hlam, p660_0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h647, hlam, p660_0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h649, hlam, p660_0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h651, hlam, p660_0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [hc23, hlam, hphi, p660_1, u2ehi0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [hc23, hlam, hphi, p660_1, u2ehi1]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [hlam, p660_0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [hc23, hlam, hphi, p660_1, u2ehi3]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h0, h642, hc23, hlam, hphi, p660_1, u2ehi1]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h0, hc24, hlam, hphi, p660_1, u2ehi1]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [hc24, hlam, hphi, p660_1, u2ehi1]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h656, hlam, p660_0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [hlam, p660_0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h0, h642, h656, hc23, hlam, hphi, p660_1, u2ehi1]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h0, hc25, hlam, hphi, p660_1, u2ehi1]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [hc25, hlam, hphi, p660_1, u2ehi1]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h657, hlam, p660_0]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [h658, hlam, p660_1]
                                        · have p660_0 := h660c.1
                                          have p660_1 := h660c.2.1
                                          have p660_2 := h660c.2.2.1
                                          have p660_3 := h660c.2.2.2
                                          linarith only [hlam, p660_0]
                                      · rcases h2bigk with h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h3, hc23, hlam, hphi, p686_1, u2ehi1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h3, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h640, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h642, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h0, hlam, p686_1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h647, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h649, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h651, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hc23, hlam, hphi, p686_1, u2ehi0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hc23, hlam, hphi, p686_1, u2ehi1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hc23, hlam, hphi, p686_1, u2ehi3]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h0, h642, hc23, hlam, hphi, p686_1, u2ehi1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h0, hc24, hlam, hphi, p686_1, u2ehi1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hc24, hlam, hphi, p686_1, u2ehi1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h656, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h0, h642, h656, hc23, hlam, hphi, p686_1, u2ehi1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h0, hc25, hlam, hphi, p686_1, u2ehi1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hc25, hlam, hphi, p686_1, u2ehi1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h657, hlam, p686_0]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [h658, hlam, p686_1]
                                        · have p686_0 := h686c.1
                                          have p686_1 := h686c.2.1
                                          have p686_2 := h686c.2.2.1
                                          have p686_3 := h686c.2.2.2
                                          linarith only [hlam, p686_0]
                                    · linarith only [h1, h653, h655, h658, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · linarith only [h0, h3, h657, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h0, h3, h656, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h3, h644, h646, h649, h655, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h3, h645, h647, h654, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h3, h644, h647, h653, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h718 | h718
                    · linarith only [h0, h640, h718, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h720 | h720
                      · linarith only [h0, h3, h720, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h722 | h722
                        · linarith only [h0, h640, h646, h722, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h724 | h724
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h725 | h725
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h726 | h726
                              · linarith only [h1, h640, h646, h724, h726, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h728 | h728
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h729 | h729
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h730 | h730
                                    · linarith only [h0, h640, h646, h730, hc24, hlam, hphi, u2ehi1]
                                    · linarith only [h0, h640, h730, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                  · linarith only [h0, h3, h729, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h0, h3, h728, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h3, h645, h718, h725, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h3, h644, h718, h724, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h737 | h737
                  · linarith only [h644, h645, h737, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h739 | h739
                    · linarith only [h0, h640, h739, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h741 | h741
                      · linarith only [h0, h640, h741, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h743 | h743
                        · linarith only [h0, h642, h743, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h745 | h745
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h746 | h746
                            · linarith only [h1, h640, h644, h645, h746, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h748 | h748
                              · linarith only [h0, h640, h737, h741, h748, hc24, hlam, hphi, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h750 | h750
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h751 | h751
                                  · linarith only [h0, h640, h644, h645, h751, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h3, h751, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h0, h1, h3, h745, h750, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · linarith only [h644, h645, h745, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h756 | h756
                · rcases m.htr 0 4 5 (by decide) (by decide) with h757 | h757
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h758 | h758
                    · linarith only [h0, h640, h758, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h760 | h760
                      · linarith only [h0, h3, h760, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h762 | h762
                        · linarith only [h0, h642, h644, h756, h762, hc34, hlam, hphi, ht23, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h764 | h764
                          · linarith only [h1, h642, h644, h756, h764, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h766 | h766
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h767 | h767
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h768 | h768
                                · linarith only [h0, h642, h644, h756, h768, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h3, h768, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h640, h757, h760, h767, hc24, hlam, hphi, u2ehi1]
                            · linarith only [h644, h756, h766, hc13, hc34, hlam, hphi]
                  · linarith only [h644, h756, h757, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h774 | h774
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h775 | h775
                    · linarith only [h0, h3, h775, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h777 | h777
                      · linarith only [h0, h3, h777, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h779 | h779
                        · linarith only [h1, h642, h756, h775, h779, hc35, hlam, hphi, ht23, u2ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h781 | h781
                          · linarith only [h1, h644, h781, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h783 | h783
                            · linarith only [h1, h756, h783, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h785 | h785
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h786 | h786
                                · linarith only [h0, h3, h644, h786, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h3, h786, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h644, h774, h777, h785, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h790 | h790
                    · linarith only [h0, h3, h790, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h792 | h792
                      · linarith only [h0, h3, h792, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h794 | h794
                        · linarith only [h0, h642, h794, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h796 | h796
                          · linarith only [h1, h644, h796, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h798 | h798
                            · linarith only [h1, h756, h798, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h800 | h800
                              · linarith only [h3, h644, h774, h792, h800, hc24, hlam, hphi, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h802 | h802
                                · linarith only [h0, h3, h644, h802, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h3, h802, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h805 | h805
        · rcases m.htr 0 2 4 (by decide) (by decide) with h806 | h806
          · rcases m.htr 0 2 5 (by decide) (by decide) with h807 | h807
            · linarith only [h0, h2, h807, hlam]
            · linarith only [h805, h807, hc25, hlam, hphi, u2ehi2]
          · linarith only [h805, h806, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h811 | h811
          · linarith only [h805, h811, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h813 | h813
            · linarith only [h805, h813, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h815 | h815
              · rcases m.htr 0 3 5 (by decide) (by decide) with h816 | h816
                · linarith only [h1, h2, h816, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h818 | h818
                  · linarith only [h0, h2, h815, h816, h818, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h820 | h820
                    · linarith only [h0, h811, h815, h816, h820, hc35, hlam, hphi, ht23, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h822 | h822
                      · linarith only [h0, h811, h822, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h824 | h824
                        · linarith only [h1, h2, h813, h820, h824, hlam]
                        · linarith only [h1, h2, h820, h824, hc25, hlam, hphi, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h827 | h827
                · linarith only [h0, h2, h815, h827, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h829 | h829
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h830 | h830
                    · linarith only [h0, h805, h830, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h832 | h832
                      · linarith only [h1, h2, h811, h829, h830, h832, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h834 | h834
                        · linarith only [h1, h2, h830, h834, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · linarith only [h1, h2, h830, h834, hc25, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h837 | h837
                    · linarith only [h0, h805, h837, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h839 | h839
                      · linarith only [h1, h2, h837, h839, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h841 | h841
                        · linarith only [h1, h2, h837, h841, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · linarith only [h1, h2, h837, h841, hc25, hlam, hphi, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h844 | h844
      · rcases m.htr 0 2 3 (by decide) (by decide) with h845 | h845
        · linarith only [h0, h1, h845, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h847 | h847
          · linarith only [h845, h847, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h849 | h849
            · linarith only [h845, h849, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h851 | h851
              · rcases m.htr 0 3 5 (by decide) (by decide) with h852 | h852
                · rcases m.htr 0 4 5 (by decide) (by decide) with h853 | h853
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h854 | h854
                    · linarith only [h0, h1, h845, h854, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h854, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h857 | h857
                    · linarith only [h0, h1, h857, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h857, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h852, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h851, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h862 | h862
        · linarith only [h0, h1, h862, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h864 | h864
          · linarith only [h862, h864, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h866 | h866
            · linarith only [h862, h866, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h868 | h868
              · rcases m.htr 0 3 5 (by decide) (by decide) with h869 | h869
                · rcases m.htr 0 4 5 (by decide) (by decide) with h870 | h870
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h871 | h871
                    · linarith only [h0, h1, h862, h871, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h871, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h874 | h874
                    · linarith only [h0, h1, h874, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h874, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h869, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h868, hc34, hlam, hphi, ht23, u2ehi1]
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s0 m hb2 hb3 hb5 h0

end R2N4
