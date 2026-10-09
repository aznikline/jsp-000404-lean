import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5218000 in
private theorem n8l_sBT8_H_R_M_IR_s12 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 6 ∧ m.d 0 1 < m.d 0 6 ∧ m.d 0 6 < m.d 1 6))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 6 ∧ m.d 0 2 < m.d 0 6 ∧ m.d 0 6 < m.d 2 6))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 3 + m.lam ≤ m.d 3 6 ∧ m.d 0 3 < m.d 0 6 ∧ m.d 0 6 < m.d 3 6))
    (hg10 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg11 : (m.d 0 4 + m.lam ≤ m.d 4 6 ∧ m.d 0 4 < m.d 0 6 ∧ m.d 0 6 < m.d 4 6))
    (hg12 : (m.d 0 5 + m.lam ≤ m.d 5 6 ∧ m.d 0 5 < m.d 0 6 ∧ m.d 0 6 < m.d 5 6))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
  · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
    · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
      · rcases m.htr 1 2 6 (by decide) (by decide) with h16 | h16
        · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
          · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 3 6 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 1 4 6 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h25 | h25
                          · linarith only [h0, h13, h25, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · linarith only [h0, h13, h19, h23, h25, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · linarith only [h0, h13, h18, h23, h24, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                        · linarith only [h0, h13, h17, h23, h29, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h31 | h31
                          · linarith only [h0, h13, h17, h23, h31, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h34 | h34
                              · linarith only [h0, h14, h34, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · linarith only [h0, h13, h17, h21, h33, h34, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h37 | h37
                              · linarith only [h0, h13, h17, h20, h33, h37, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h39 | h39
                                · linarith only [h0, h15, h39, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                                  · linarith only [h0, h13, h17, h23, h33, h41, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                  · linarith only [h0, h13, h17, h20, h23, h41, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h46 | h46
                          · linarith only [h0, h13, h46, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · linarith only [h0, h13, h19, h45, h46, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h0, h13, h18, h44, h45, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h50 | h50
                        · linarith only [h0, h13, h17, h44, h50, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h52 | h52
                          · linarith only [h0, h10, h12, h18, h22, h3, h50, h52, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h55 | h55
                              · linarith only [h0, h14, h55, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · linarith only [h0, h13, h17, h21, h54, h55, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h58 | h58
                              · linarith only [h0, h10, h12, h20, h22, h3, h54, h58, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h60 | h60
                                · linarith only [h0, h20, h22, h44, h5, h54, h60, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                                  · linarith only [h0, h13, h17, h44, h54, h62, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                  · linarith only [h20, h22, h44, h62, hc23, hc56, hlam, hphi, ht34, ht45]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h65 | h65
                    · linarith only [h0, h11, h20, h21, h3, h65, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h69 | h69
                          · linarith only [h0, h13, h69, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · linarith only [h0, h13, h19, h67, h69, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · linarith only [h0, h13, h18, h67, h68, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
                        · linarith only [h0, h11, h17, h21, h3, h67, h7, h73, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h75 | h75
                          · linarith only [h0, h11, h18, h20, h21, h3, h7, h73, h75, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h77 | h77
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h78 | h78
                              · linarith only [h0, h18, h20, h21, h4, h73, h78, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h80 | h80
                                · linarith only [h0, h15, h65, h80, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h82 | h82
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h83 | h83
                                    · linarith only [h17, h21, h83, hlam]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h85 | h85
                                      · linarith only [h18, h65, h85, hlam]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h87 | h87
                                        · linarith only [h18, h65, h73, h87, hc23, hc45, hlam, hphi, ht34]
                                        · rcases h6bigk with h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            rcases p89_3 (m.d 0 6) (by simp) with h91 | h91
                                            · rcases p89_3 (m.d 1 6) (by simp) with h92 | h92
                                              · linarith only [h2, h92, hlam]
                                              · rcases p89_3 (m.d 2 6) (by simp) with h94 | h94
                                                · linarith only [h6, h94, hlam]
                                                · rcases p89_3 (m.d 3 6) (by simp) with h96 | h96
                                                  · linarith only [h9, h96, hlam]
                                                  · rcases p89_3 (m.d 4 6) (by simp) with h98 | h98
                                                    · linarith only [h11, h98, hlam]
                                                    · linarith only [h21, h98, hlam]
                                            · linarith only [h2, h91, hlam]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            rcases p89_3 (m.d 0 6) (by simp) with h102 | h102
                                            · rcases p89_3 (m.d 1 6) (by simp) with h103 | h103
                                              · linarith only [h103, h2, hlam]
                                              · linarith only [h103, h16, hlam]
                                            · linarith only [h102, h6, hlam]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            rcases p89_3 (m.d 0 6) (by simp) with h107 | h107
                                            · rcases p89_3 (m.d 1 6) (by simp) with h108 | h108
                                              · linarith only [h108, h2, hlam]
                                              · linarith only [h108, h19, hlam]
                                            · linarith only [h107, h9, hlam]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h0, h10, h12, h18, h20, h21, h3, h7, h73, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p89_1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h0, h10, h12, h18, h20, h21, h3, h7, h73, h87, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p89_1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h2, hlam, p89_1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p89_1, u6ehi2]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h0, h13, h19, h75, h77, h78, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p89_1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h21, hlam, p89_1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h65, hlam, p89_1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h6, hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h16, hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h75, hlam, p89_1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h78, hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h80, hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h9, hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h19, hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h0, h3, h77, h78, h9, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p89_1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h83, hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h85, hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h11, hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p89_1, u6ehi1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h0, h10, h12, h3, h7, h77, h78, h87, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p89_1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h0, h10, h12, h3, h7, h87, hc01, hlam, hphi, ht0b, ht6b, p89_1, u6ehi3]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h87, hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h12, hlam, p89_0]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h0, h10, h12, h18, h20, h21, h3, h7, h73, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p89_1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h0, h10, h12, h3, h7, h77, h78, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p89_1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h0, h10, h12, h3, h7, h73, h82, h83, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p89_1]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p89_1, u6ehi4]
                                          · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                            linarith only [hlam, p89_0]
                                  · linarith only [h0, h14, h77, h82, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                            · linarith only [h20, h21, h77, hc24, hc46, hlam, hphi]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h146 | h146
                  · linarith only [h0, h10, h146, h20, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h148 | h148
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h149 | h149
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h150 | h150
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h151 | h151
                          · linarith only [h0, h13, h151, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · linarith only [h0, h13, h150, h151, h19, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h0, h13, h149, h150, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h155 | h155
                        · linarith only [h0, h13, h149, h155, h17, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h157 | h157
                          · linarith only [h0, h10, h149, h157, h17, h20, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h159 | h159
                            · linarith only [h0, h149, h159, h17, h20, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h161 | h161
                              · linarith only [h0, h146, h149, h161, h17, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h163 | h163
                                · linarith only [h0, h13, h155, h163, h18, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h165 | h165
                                  · linarith only [h148, h149, h159, h163, h165, h20, hc23, hc34, hlam, hphi]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h167 | h167
                                    · linarith only [h146, h167, h17, hlam]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h169 | h169
                                      · linarith only [h0, h13, h149, h159, h163, h169, h18, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                      · linarith only [h0, h148, h15, h155, h169, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h173 | h173
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h174 | h174
                          · linarith only [h0, h13, h174, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · linarith only [h0, h13, h173, h174, h19, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h0, h13, h172, h173, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                        · linarith only [h0, h10, h12, h148, h17, h172, h178, h20, h3, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h180 | h180
                          · linarith only [h0, h10, h12, h148, h17, h172, h180, h20, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h182 | h182
                            · linarith only [h0, h17, h172, h182, h20, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h184 | h184
                              · linarith only [h0, h14, h184, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h186 | h186
                                · linarith only [h0, h148, h15, h186, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                                  · linarith only [h17, h188, h20, hlam]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h190 | h190
                                    · linarith only [h146, h17, h190, hlam]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h192 | h192
                                      · linarith only [h148, h18, h192, hlam]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h194 | h194
                                        · linarith only [h148, h17, h172, h194, h20, hc23, hc45, hlam, hphi, ht34]
                                        · linarith only [h17, h172, h194, h20, hc23, hc56, hlam, hphi, ht34, ht45]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h197 | h197
                · rcases m.htr 1 4 6 (by decide) (by decide) with h198 | h198
                  · linarith only [h0, h17, h19, h198, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h200 | h200
                    · linarith only [h0, h17, h19, h197, h200, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h204 | h204
                          · linarith only [h13, h19, h204, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h207 | h207
                              · linarith only [h0, h14, h198, h207, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h209 | h209
                                · linarith only [h0, h15, h200, h209, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h211 | h211
                                  · linarith only [h0, h17, h19, h211, h3, h9, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                  · linarith only [h0, h14, h206, h211, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                            · linarith only [h0, h11, h197, h198, h206, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · linarith only [h0, h18, h19, h203, h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                      · linarith only [h0, h17, h19, h202, h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h217 | h217
                  · linarith only [h0, h18, h19, h197, h217, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h219 | h219
                    · linarith only [h0, h18, h19, h219, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h221 | h221
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h222 | h222
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h223 | h223
                          · linarith only [h0, h13, h19, h223, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h225 | h225
                            · linarith only [h0, h14, h197, h225, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h227 | h227
                              · linarith only [h0, h14, h217, h227, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h229 | h229
                                · linarith only [h0, h15, h229, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h231 | h231
                                  · linarith only [h0, h13, h19, h221, h231, h3, h9, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h233 | h233
                                    · linarith only [h0, h17, h19, h217, h233, h3, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h235 | h235
                                      · linarith only [h0, h11, h13, h19, h222, h233, h235, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h237 | h237
                                        · linarith only [h0, h10, h13, h19, h222, h235, h237, h3, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                        · rcases h6bigk with h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            rcases p239_3 (m.d 0 6) (by simp) with h241 | h241
                                            · rcases p239_3 (m.d 1 6) (by simp) with h242 | h242
                                              · linarith only [h2, h242, hlam]
                                              · rcases p239_3 (m.d 2 6) (by simp) with h244 | h244
                                                · linarith only [h244, h6, hlam]
                                                · rcases p239_3 (m.d 3 6) (by simp) with h246 | h246
                                                  · linarith only [h246, h9, hlam]
                                                  · linarith only [h19, h246, hlam]
                                            · linarith only [h2, h241, hlam]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            rcases p239_3 (m.d 0 6) (by simp) with h250 | h250
                                            · rcases p239_3 (m.d 1 6) (by simp) with h251 | h251
                                              · linarith only [h2, h251, hlam]
                                              · linarith only [h16, h251, hlam]
                                            · linarith only [h250, h6, hlam]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h0, h10, h12, h13, h19, h222, h231, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h0, h10, h12, h13, h19, h222, h231, h233, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h0, h10, h12, h14, h197, h221, h237, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h2, hlam, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p239_1, u6ehi2]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h19, hlam, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h217, hlam, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h219, hlam, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h6, hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h16, hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h223, hlam, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h227, hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h229, hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h9, hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p239_1, u6ehi1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p239_1, u6ehi2]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h233, hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h235, hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h11, hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h0, h11, h13, h19, h222, h231, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h0, h11, h222, h223, h231, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p239_1, u6ehi3]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h237, hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h12, hlam, p239_0]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h13, h19, h222, h231, hc34, hc56, hlam, hphi, ht45, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h0, h10, h12, h222, h223, h231, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h0, h10, h12, h13, h19, h222, h231, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p239_1]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p239_1, u6ehi4]
                                          · obtain ⟨p239_0, p239_1, p239_2, p239_3⟩ := h239c
                                            linarith only [hlam, p239_0]
                        · linarith only [h18, h19, h222, hc23, hc36, hlam, hphi]
                      · linarith only [h0, h17, h19, h221, h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
            · rcases m.htr 1 3 6 (by decide) (by decide) with h290 | h290
              · linarith only [h0, h18, h290, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h292 | h292
                · linarith only [h17, h18, h292, hlam]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h294 | h294
                  · linarith only [h0, h17, h18, h294, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h296 | h296
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h297 | h297
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h298 | h298
                        · linarith only [h0, h13, h18, h298, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h300 | h300
                          · linarith only [h13, h290, h300, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h302 | h302
                            · linarith only [h0, h292, h296, h302, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h304 | h304
                              · linarith only [h14, h294, h304, hlam]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h306 | h306
                                · linarith only [h0, h15, h306, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                · linarith only [h0, h15, h296, h297, h298, h306, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h17, h290, h297, hc23, hc36, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h311 | h311
                        · linarith only [h0, h13, h18, h311, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h313 | h313
                          · linarith only [h0, h13, h313, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h315 | h315
                            · linarith only [h14, h292, h315, hlam]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h317 | h317
                              · linarith only [h14, h294, h317, hlam]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h319 | h319
                                · linarith only [h0, h15, h296, h319, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h321 | h321
                                  · linarith only [h0, h292, h3, h310, h321, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h323 | h323
                                    · linarith only [h13, h18, h294, h296, h310, h323, hlam]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h325 | h325
                                      · linarith only [h13, h18, h296, h310, h321, h325, hc34, hc45, hlam, hphi]
                                      · linarith only [h0, h10, h12, h13, h18, h3, h310, h325, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h17, h18, h310, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h329 | h329
            · rcases m.htr 1 3 6 (by decide) (by decide) with h330 | h330
              · linarith only [h0, h17, h3, h330, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h332 | h332
                · rcases m.htr 1 4 6 (by decide) (by decide) with h333 | h333
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h334 | h334
                    · linarith only [h0, h17, h3, h329, h334, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h336 | h336
                      · linarith only [h0, h17, h3, h329, h336, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h338 | h338
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h339 | h339
                          · linarith only [h0, h13, h17, h3, h339, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h341 | h341
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h342 | h342
                              · linarith only [h0, h14, h342, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · linarith only [h0, h14, h333, h341, h342, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · linarith only [h0, h10, h12, h3, h332, h334, h336, h338, h341, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h0, h17, h3, h329, h338, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h347 | h347
                    · linarith only [h0, h11, h17, h3, h329, h333, h347, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h349 | h349
                      · linarith only [h0, h17, h3, h329, h349, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h351 | h351
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h352 | h352
                          · linarith only [h0, h13, h17, h3, h352, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h354 | h354
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h355 | h355
                              · linarith only [h14, h333, h355, hlam]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h357 | h357
                                · linarith only [h0, h11, h15, h17, h3, h329, h333, h347, h357, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h359 | h359
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h360 | h360
                                    · linarith only [h0, h17, h3, h329, h333, h359, h360, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                    · linarith only [h0, h11, h13, h17, h3, h351, h359, h360, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                  · linarith only [h0, h10, h13, h17, h3, h351, h359, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                            · linarith only [h0, h11, h3, h332, h333, h354, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · linarith only [h0, h17, h3, h329, h351, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                · linarith only [h17, h329, h332, hlam]
            · rcases m.htr 1 3 6 (by decide) (by decide) with h367 | h367
              · linarith only [h0, h3, h329, h367, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h369 | h369
                · rcases m.htr 1 4 6 (by decide) (by decide) with h370 | h370
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h371 | h371
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h372 | h372
                      · linarith only [h13, h17, h372, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h374 | h374
                        · linarith only [h13, h329, h374, hlam]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h376 | h376
                          · linarith only [h13, h367, h376, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h378 | h378
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h379 | h379
                              · linarith only [h0, h14, h379, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · linarith only [h0, h14, h370, h378, h379, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h382 | h382
                              · linarith only [h0, h17, h3, h369, h378, h382, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h384 | h384
                                · linarith only [h0, h15, h384, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h386 | h386
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h387 | h387
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h388 | h388
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h389 | h389
                                        · linarith only [h0, h17, h3, h369, h372, h378, h384, h389, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                        · linarith only [h0, h17, h3, h369, h371, h372, h378, h389, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                      · linarith only [h0, h17, h3, h329, h369, h371, h388, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                    · linarith only [h17, h370, h387, hlam]
                                  · linarith only [h0, h10, h17, h3, h369, h371, h384, h386, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h395 | h395
                      · linarith only [h1, h13, h17, h370, h395, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h397 | h397
                        · linarith only [h0, h13, h329, h397, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h399 | h399
                          · linarith only [h0, h13, h3, h329, h399, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h401 | h401
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h402 | h402
                              · linarith only [h0, h14, h402, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · linarith only [h0, h14, h370, h401, h402, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h405 | h405
                              · linarith only [h0, h10, h12, h3, h369, h371, h401, h405, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h407 | h407
                                · linarith only [h0, h369, h371, h395, h401, h407, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h409 | h409
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h410 | h410
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h411 | h411
                                      · linarith only [h0, h3, h369, h371, h395, h401, h409, h411, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h413 | h413
                                        · linarith only [h329, h369, h411, h413, hlam]
                                        · rcases h6bigk with h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            rcases p415_3 (m.d 0 6) (by simp) with h417 | h417
                                            · rcases p415_3 (m.d 1 6) (by simp) with h418 | h418
                                              · linarith only [h2, h418, hlam]
                                              · rcases p415_3 (m.d 2 6) (by simp) with h420 | h420
                                                · linarith only [h420, h6, hlam]
                                                · rcases p415_3 (m.d 3 6) (by simp) with h422 | h422
                                                  · linarith only [h422, h9, hlam]
                                                  · linarith only [h367, h422, hlam]
                                            · linarith only [h2, h417, hlam]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            rcases p415_3 (m.d 0 6) (by simp) with h426 | h426
                                            · rcases p415_3 (m.d 1 6) (by simp) with h427 | h427
                                              · linarith only [h2, h427, hlam]
                                              · linarith only [h16, h427, hlam]
                                            · linarith only [h426, h6, hlam]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            rcases p415_3 (m.d 0 6) (by simp) with h431 | h431
                                            · rcases p415_3 (m.d 1 6) (by simp) with h432 | h432
                                              · linarith only [h2, h432, hlam]
                                              · rcases p415_3 (m.d 2 6) (by simp) with h434 | h434
                                                · linarith only [h434, h6, hlam]
                                                · rcases p415_3 (m.d 3 6) (by simp) with h436 | h436
                                                  · linarith only [h436, h9, hlam]
                                                  · rcases p415_3 (m.d 4 6) (by simp) with h438 | h438
                                                    · linarith only [h11, h438, hlam]
                                                    · rcases p415_3 (m.d 5 6) (by simp) with h440 | h440
                                                      · linarith only [h12, h440, hlam]
                                                      · linarith only [h411, h440, hlam]
                                            · linarith only [h431, h9, hlam]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            rcases p415_3 (m.d 0 6) (by simp) with h444 | h444
                                            · rcases p415_3 (m.d 1 6) (by simp) with h445 | h445
                                              · linarith only [h2, h445, hlam]
                                              · linarith only [h370, h445, hlam]
                                            · linarith only [h11, h444, hlam]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h0, h10, h12, h3, h329, h369, h395, h401, h411, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p415_1]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h2, hlam, p415_1]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p415_1, u6ehi2]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h367, hlam, p415_1]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h0, h17, h3, h370, h395, h401, h413, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p415_1]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h371, hlam, p415_1]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h6, hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h16, hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h399, hlam, p415_1]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h405, hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h407, hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h9, hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p415_1, u6ehi1]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p415_1, u6ehi2]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h0, h3, h395, h401, h410, h413, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p415_1]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h411, hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h11, hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h370, hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h2, h370, hc01, hlam, hphi, ht0b, ht6b, p415_1, u6ehi2]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h410, hlam, p415_1]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h413, hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h12, hlam, p415_0]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p415_1, u6ehi1]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p415_1, u6ehi2]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p415_1, u6ehi3]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p415_1, u6ehi4]
                                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                            linarith only [hlam, p415_0]
                                    · linarith only [h0, h11, h17, h3, h369, h395, h401, h410, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                  · linarith only [h17, h369, h409, hlam]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h482 | h482
                    · linarith only [h0, h11, h3, h369, h370, h482, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h484 | h484
                      · linarith only [h0, h13, h17, h369, h484, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h486 | h486
                        · linarith only [h13, h329, h486, hlam]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h488 | h488
                          · linarith only [h13, h367, h488, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h490 | h490
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h491 | h491
                              · linarith only [h0, h14, h491, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h493 | h493
                                · linarith only [h0, h15, h329, h482, h493, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h495 | h495
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h496 | h496
                                    · linarith only [h0, h14, h3, h370, h490, h496, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h498 | h498
                                      · linarith only [h0, h11, h13, h3, h329, h482, h495, h496, h498, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h500 | h500
                                        · linarith only [h14, h2, h370, h490, h498, h500, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                        · rcases h6bigk with h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            rcases p502_3 (m.d 0 6) (by simp) with h504 | h504
                                            · rcases p502_3 (m.d 1 6) (by simp) with h505 | h505
                                              · linarith only [h2, h505, hlam]
                                              · rcases p502_3 (m.d 2 6) (by simp) with h507 | h507
                                                · linarith only [h507, h6, hlam]
                                                · rcases p502_3 (m.d 3 6) (by simp) with h509 | h509
                                                  · linarith only [h509, h9, hlam]
                                                  · linarith only [h367, h509, hlam]
                                            · linarith only [h2, h504, hlam]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            rcases p502_3 (m.d 0 6) (by simp) with h513 | h513
                                            · rcases p502_3 (m.d 1 6) (by simp) with h514 | h514
                                              · linarith only [h2, h514, hlam]
                                              · linarith only [h16, h514, hlam]
                                            · linarith only [h513, h6, hlam]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            rcases p502_3 (m.d 0 6) (by simp) with h518 | h518
                                            · rcases p502_3 (m.d 1 6) (by simp) with h519 | h519
                                              · linarith only [h2, h519, hlam]
                                              · rcases p502_3 (m.d 2 6) (by simp) with h521 | h521
                                                · linarith only [h521, h6, hlam]
                                                · rcases p502_3 (m.d 3 6) (by simp) with h523 | h523
                                                  · linarith only [h523, h9, hlam]
                                                  · rcases p502_3 (m.d 4 6) (by simp) with h525 | h525
                                                    · linarith only [h11, h525, hlam]
                                                    · linarith only [h496, h525, hlam]
                                            · linarith only [h518, h9, hlam]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h0, h10, h12, h3, h369, h370, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p502_1]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h0, h10, h12, h13, h3, h329, h498, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p502_1]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h2, hlam, p502_1]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p502_1, u6ehi2]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h367, hlam, p502_1]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h370, hlam, p502_1]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h482, hlam, p502_1]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h6, hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h16, hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h488, hlam, p502_1]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h491, hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h493, hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h9, hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p502_1, u6ehi1]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p502_1, u6ehi2]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h496, hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h498, hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h11, hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h0, h11, h14, h3, h370, h490, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p502_1]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p502_1, u6ehi2]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p502_1, u6ehi3]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h500, hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h12, hlam, p502_0]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h14, h370, h490, hc45, hc56, hlam, hphi, p502_1]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h0, h10, h12, h3, h490, h491, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p502_1]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h0, h10, h12, h13, h3, h329, h495, h496, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p502_1]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p502_1, u6ehi4]
                                          · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                            linarith only [hlam, p502_0]
                                  · linarith only [h14, h370, h490, h495, hc34, hc46, hlam, hphi]
                            · linarith only [h0, h11, h3, h369, h370, h490, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h563 | h563
                  · linarith only [h0, h10, h3, h369, h563, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h565 | h565
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h566 | h566
                      · linarith only [h13, h17, h566, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h568 | h568
                        · linarith only [h0, h13, h329, h568, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h570 | h570
                          · linarith only [h0, h13, h367, h570, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h572 | h572
                            · linarith only [h14, h369, h572, hlam]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h574 | h574
                              · linarith only [h14, h563, h574, hlam]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h576 | h576
                                · linarith only [h0, h15, h576, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h578 | h578
                                  · linarith only [h0, h3, h369, h565, h566, h572, h576, h578, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h580 | h580
                                    · linarith only [h563, h578, h580, hc14, hc45, hlam, hphi]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h582 | h582
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h583 | h583
                                        · rcases h6bigk with h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            rcases p584_3 (m.d 0 6) (by simp) with h586 | h586
                                            · rcases p584_3 (m.d 1 6) (by simp) with h587 | h587
                                              · linarith only [h2, h587, hlam]
                                              · rcases p584_3 (m.d 2 6) (by simp) with h589 | h589
                                                · linarith only [h589, h6, hlam]
                                                · rcases p584_3 (m.d 3 6) (by simp) with h591 | h591
                                                  · linarith only [h591, h9, hlam]
                                                  · linarith only [h367, h591, hlam]
                                            · linarith only [h2, h586, hlam]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            rcases p584_3 (m.d 0 6) (by simp) with h595 | h595
                                            · rcases p584_3 (m.d 1 6) (by simp) with h596 | h596
                                              · linarith only [h2, h596, hlam]
                                              · linarith only [h16, h596, hlam]
                                            · linarith only [h595, h6, hlam]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            rcases p584_3 (m.d 0 6) (by simp) with h600 | h600
                                            · rcases p584_3 (m.d 1 6) (by simp) with h601 | h601
                                              · linarith only [h2, h601, hlam]
                                              · rcases p584_3 (m.d 2 6) (by simp) with h603 | h603
                                                · linarith only [h6, h603, hlam]
                                                · rcases p584_3 (m.d 3 6) (by simp) with h605 | h605
                                                  · linarith only [h605, h9, hlam]
                                                  · rcases p584_3 (m.d 4 6) (by simp) with h607 | h607
                                                    · linarith only [h11, h607, hlam]
                                                    · linarith only [h580, h607, hlam]
                                            · linarith only [h600, h9, hlam]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h0, h10, h12, h17, h3, h580, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p584_1]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            rcases p584_3 (m.d 0 6) (by simp) with h612 | h612
                                            · rcases p584_3 (m.d 1 6) (by simp) with h613 | h613
                                              · linarith only [h2, h613, hlam]
                                              · linarith only [h565, h613, hlam]
                                            · linarith only [h12, h612, hlam]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h2, hlam, p584_1]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p584_1, u6ehi2]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h367, hlam, p584_1]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h563, hlam, p584_1]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h367, h566, h572, h576, hc23, hc36, hlam, hphi, p584_1]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h6, hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h16, hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h570, hlam, p584_1]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h574, hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h576, hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h9, hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p584_1, u6ehi1]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p584_1, u6ehi2]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h580, hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h566, h572, h576, h582, hc23, hc35, hlam, hphi, p584_1]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h11, hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h0, h11, h3, h565, h566, h572, h576, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p584_1]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p584_1, u6ehi2]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p584_1, u6ehi3]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h0, h10, h3, h566, h572, h576, h583, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p584_1]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h12, hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h565, hlam, p584_0]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h565, hc15, hlam, hphi, ht01, ht0b, ht6b, p584_1, u6ehi2]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h582, hlam, p584_1]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [h583, hlam, p584_1]
                                          · obtain ⟨p584_0, p584_1, p584_2, p584_3⟩ := h584c
                                            linarith only [hlam, p584_0]
                                        · linarith only [h329, h565, h578, h583, hlam]
                                      · linarith only [h329, h565, h582, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h649 | h649
                      · linarith only [h13, h17, h649, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h651 | h651
                        · linarith only [h13, h329, h651, hlam]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h653 | h653
                          · linarith only [h0, h13, h17, h3, h653, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h655 | h655
                            · linarith only [h14, h369, h655, hlam]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h657 | h657
                              · linarith only [h0, h10, h12, h14, h3, h369, h565, h657, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h659 | h659
                                · linarith only [h15, h565, h659, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h661 | h661
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h662 | h662
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h663 | h663
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h664 | h664
                                        · linarith only [h0, h14, h3, h369, h565, h649, h661, h664, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                        · linarith only [h14, h369, h649, h663, h664, hc23, hc35, hlam, hphi]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h667 | h667
                                        · linarith only [h0, h10, h3, h329, h663, h667, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                        · rcases h6bigk with h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            rcases p669_3 (m.d 0 6) (by simp) with h671 | h671
                                            · rcases p669_3 (m.d 1 6) (by simp) with h672 | h672
                                              · linarith only [h2, h672, hlam]
                                              · rcases p669_3 (m.d 2 6) (by simp) with h674 | h674
                                                · linarith only [h6, h674, hlam]
                                                · rcases p669_3 (m.d 3 6) (by simp) with h676 | h676
                                                  · linarith only [h676, h9, hlam]
                                                  · linarith only [h367, h676, hlam]
                                            · linarith only [h2, h671, hlam]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            rcases p669_3 (m.d 0 6) (by simp) with h680 | h680
                                            · rcases p669_3 (m.d 1 6) (by simp) with h681 | h681
                                              · linarith only [h2, h681, hlam]
                                              · linarith only [h16, h681, hlam]
                                            · linarith only [h6, h680, hlam]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            rcases p669_3 (m.d 0 6) (by simp) with h685 | h685
                                            · rcases p669_3 (m.d 1 6) (by simp) with h686 | h686
                                              · linarith only [h2, h686, hlam]
                                              · rcases p669_3 (m.d 2 6) (by simp) with h688 | h688
                                                · linarith only [h6, h688, hlam]
                                                · rcases p669_3 (m.d 3 6) (by simp) with h690 | h690
                                                  · linarith only [h690, h9, hlam]
                                                  · rcases p669_3 (m.d 4 6) (by simp) with h692 | h692
                                                    · linarith only [h11, h692, hlam]
                                                    · rcases p669_3 (m.d 5 6) (by simp) with h694 | h694
                                                      · linarith only [h12, h694, hlam]
                                                      · linarith only [h663, h694, hlam]
                                            · linarith only [h685, h9, hlam]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            rcases p669_3 (m.d 0 6) (by simp) with h698 | h698
                                            · rcases p669_3 (m.d 1 6) (by simp) with h699 | h699
                                              · linarith only [h2, h699, hlam]
                                              · rcases p669_3 (m.d 2 6) (by simp) with h701 | h701
                                                · linarith only [h6, h701, hlam]
                                                · rcases p669_3 (m.d 3 6) (by simp) with h703 | h703
                                                  · linarith only [h703, h9, hlam]
                                                  · linarith only [h662, h703, hlam]
                                            · linarith only [h11, h698, hlam]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h0, h10, h12, h14, h3, h369, h649, h661, h663, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p669_1]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h2, hlam, p669_1]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p669_1, u6ehi2]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h367, hlam, p669_1]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h563, hlam, p669_1]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h565, hlam, p669_1]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h6, hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h16, hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h653, hlam, p669_1]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h657, hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h659, hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h9, hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p669_1, u6ehi1]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p669_1, u6ehi2]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h0, h14, h3, h369, h649, h662, h667, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p669_1]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h663, hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h11, hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h0, h11, h16, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p669_1, u6ehi2]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p669_1, u6ehi2]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h662, hlam, p669_1]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h667, hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h12, hlam, p669_0]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h0, h10, h12, h16, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p669_1, u6ehi2]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p669_1, u6ehi2]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p669_1, u6ehi3]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p669_1, u6ehi4]
                                          · obtain ⟨p669_0, p669_1, p669_2, p669_3⟩ := h669c
                                            linarith only [hlam, p669_0]
                                    · linarith only [h0, h11, h14, h3, h369, h649, h661, h662, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h739 | h739
                                    · linarith only [h0, h10, h3, h661, h7, h739, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h741 | h741
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h742 | h742
                                        · rcases h6bigk with h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            rcases p743_3 (m.d 0 6) (by simp) with h745 | h745
                                            · rcases p743_3 (m.d 1 6) (by simp) with h746 | h746
                                              · linarith only [h2, h746, hlam]
                                              · rcases p743_3 (m.d 2 6) (by simp) with h748 | h748
                                                · linarith only [h6, h748, hlam]
                                                · rcases p743_3 (m.d 3 6) (by simp) with h750 | h750
                                                  · linarith only [h750, h9, hlam]
                                                  · linarith only [h367, h750, hlam]
                                            · linarith only [h2, h745, hlam]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            rcases p743_3 (m.d 0 6) (by simp) with h754 | h754
                                            · rcases p743_3 (m.d 1 6) (by simp) with h755 | h755
                                              · linarith only [h2, h755, hlam]
                                              · linarith only [h16, h755, hlam]
                                            · linarith only [h6, h754, hlam]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            rcases p743_3 (m.d 0 6) (by simp) with h759 | h759
                                            · rcases p743_3 (m.d 1 6) (by simp) with h760 | h760
                                              · linarith only [h2, h760, hlam]
                                              · rcases p743_3 (m.d 2 6) (by simp) with h762 | h762
                                                · linarith only [h6, h762, hlam]
                                                · rcases p743_3 (m.d 3 6) (by simp) with h764 | h764
                                                  · linarith only [h764, h9, hlam]
                                                  · rcases p743_3 (m.d 4 6) (by simp) with h766 | h766
                                                    · linarith only [h11, h766, hlam]
                                                    · linarith only [h739, h766, hlam]
                                            · linarith only [h759, h9, hlam]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h0, h10, h12, h13, h17, h3, h7, h739, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p743_1]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            rcases p743_3 (m.d 0 6) (by simp) with h771 | h771
                                            · rcases p743_3 (m.d 1 6) (by simp) with h772 | h772
                                              · linarith only [h2, h772, hlam]
                                              · rcases p743_3 (m.d 2 6) (by simp) with h774 | h774
                                                · linarith only [h6, h774, hlam]
                                                · rcases p743_3 (m.d 3 6) (by simp) with h776 | h776
                                                  · linarith only [h776, h9, hlam]
                                                  · linarith only [h741, h776, hlam]
                                            · linarith only [h12, h771, hlam]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h2, hlam, p743_1]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p743_1, u6ehi2]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h367, hlam, p743_1]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h563, hlam, p743_1]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h565, hlam, p743_1]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h6, hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h16, hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h653, hlam, p743_1]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h657, hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h659, hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h9, hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p743_1, u6ehi1]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p743_1, u6ehi2]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h739, hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h0, h10, h14, h3, h369, h565, h649, h661, h7, h741, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p743_1]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h11, hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h0, h11, h16, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p743_1, u6ehi2]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p743_1, u6ehi2]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p743_1, u6ehi3]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h0, h10, h14, h3, h369, h565, h649, h7, h742, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p743_1]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h12, hlam, p743_0]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h0, h16, h3, h741, h9, hc01, hlam, hphi, ht0b, ht6b, p743_1, u6ehi2]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p743_1, u6ehi2]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h741, hlam, p743_1]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [h742, hlam, p743_1]
                                          · obtain ⟨p743_0, p743_1, p743_2, p743_3⟩ := h743c
                                            linarith only [hlam, p743_0]
                                        · linarith only [h661, h741, h742, hlam]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h811 | h811
                                        · linarith only [h0, h10, h13, h3, h329, h7, h741, h811, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                        · linarith only [h13, h17, h661, h811, hc23, hc56, hlam, hphi, ht34, ht45]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h814 | h814
          · rcases m.htr 1 3 5 (by decide) (by decide) with h815 | h815
            · rcases m.htr 1 3 6 (by decide) (by decide) with h816 | h816
              · linarith only [h0, h13, h16, h6, h816, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h818 | h818
                · rcases m.htr 1 4 6 (by decide) (by decide) with h819 | h819
                  · linarith only [h0, h14, h16, h6, h819, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h821 | h821
                    · linarith only [h0, h15, h16, h6, h821, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h823 | h823
                      · linarith only [h0, h13, h16, h6, h823, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h13, h16, h6, h814, h823, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h826 | h826
                  · linarith only [h0, h13, h16, h6, h815, h818, h826, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h828 | h828
                    · linarith only [h0, h13, h16, h6, h815, h828, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h830 | h830
                      · linarith only [h0, h13, h16, h6, h830, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h13, h16, h6, h814, h830, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
            · rcases m.htr 1 3 6 (by decide) (by decide) with h833 | h833
              · linarith only [h0, h15, h16, h6, h815, h833, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h835 | h835
                · linarith only [h814, h815, h835, hlam]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h837 | h837
                  · linarith only [h0, h15, h16, h6, h814, h815, h837, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h839 | h839
                    · linarith only [h0, h15, h16, h6, h839, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h841 | h841
                      · linarith only [h0, h13, h16, h6, h841, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h10, h12, h3, h7, h814, h815, h839, h841, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h844 | h844
            · rcases m.htr 1 3 6 (by decide) (by decide) with h845 | h845
              · linarith only [h0, h3, h7, h814, h845, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h847 | h847
                · rcases m.htr 1 4 6 (by decide) (by decide) with h848 | h848
                  · linarith only [h0, h14, h16, h6, h848, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h850 | h850
                    · linarith only [h0, h11, h3, h7, h814, h844, h848, h850, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h852 | h852
                      · linarith only [h0, h13, h16, h6, h852, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h854 | h854
                        · linarith only [h0, h13, h16, h6, h854, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h0, h11, h3, h7, h814, h844, h848, h854, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                · linarith only [h814, h844, h847, hlam]
            · rcases m.htr 1 3 6 (by decide) (by decide) with h858 | h858
              · linarith only [h0, h3, h7, h814, h858, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h860 | h860
                · rcases m.htr 1 4 6 (by decide) (by decide) with h861 | h861
                  · linarith only [h0, h14, h16, h6, h861, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h863 | h863
                    · linarith only [h0, h11, h3, h7, h860, h861, h863, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h865 | h865
                      · linarith only [h0, h13, h16, h6, h865, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h867 | h867
                        · linarith only [h0, h14, h16, h6, h844, h865, h867, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h869 | h869
                          · linarith only [h13, h16, h858, h869, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h871 | h871
                            · linarith only [h0, h14, h16, h3, h869, h871, h9, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · linarith only [h0, h14, h16, h3, h860, h865, h869, h871, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h874 | h874
                  · linarith only [h0, h15, h16, h6, h860, h874, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h876 | h876
                    · linarith only [h0, h15, h16, h6, h876, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h878 | h878
                      · linarith only [h0, h13, h16, h6, h814, h878, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h880 | h880
                        · linarith only [h0, h13, h16, h6, h844, h860, h880, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h882 | h882
                          · linarith only [h0, h13, h3, h7, h814, h882, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h884 | h884
                            · linarith only [h0, h14, h16, h3, h882, h884, h9, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h886 | h886
                              · linarith only [h0, h15, h16, h3, h814, h874, h882, h884, h886, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h888 | h888
                                · linarith only [h0, h11, h15, h16, h3, h7, h886, h888, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h890 | h890
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h891 | h891
                                    · linarith only [h0, h15, h16, h3, h7, h886, h891, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                                    · linarith only [h0, h11, h13, h3, h7, h814, h860, h890, h891, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h894 | h894
                                    · linarith only [h0, h10, h3, h7, h890, h894, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h896 | h896
                                      · linarith only [h15, h16, h878, h884, h888, h896, hc23, hc35, hlam, hphi]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h898 | h898
                                        · linarith only [h0, h10, h13, h3, h7, h814, h890, h896, h898, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                        · linarith only [h13, h814, h890, h898, hc23, hc56, hlam, hphi, ht34, ht45]
      · rcases m.htr 1 2 6 (by decide) (by decide) with h901 | h901
        · linarith only [h0, h15, h5, h901, hc01, hlam, hphi, ht0b, ht6b, u6ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h903 | h903
          · rcases m.htr 1 3 5 (by decide) (by decide) with h904 | h904
            · linarith only [h13, h15, h904, hlam]
            · rcases m.htr 1 3 6 (by decide) (by decide) with h906 | h906
              · linarith only [h0, h13, h15, h5, h906, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h908 | h908
                · linarith only [h14, h15, h908, hlam]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h910 | h910
                  · linarith only [h0, h13, h15, h5, h903, h910, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h912 | h912
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h913 | h913
                      · linarith only [h0, h13, h15, h5, h913, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h13, h15, h5, h903, h913, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h916 | h916
                      · linarith only [h0, h10, h12, h13, h15, h3, h7, h912, h916, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h10, h12, h13, h15, h3, h7, h903, h912, h916, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h919 | h919
            · linarith only [h14, h15, h903, h919, hlam]
            · rcases m.htr 1 3 6 (by decide) (by decide) with h921 | h921
              · linarith only [h0, h14, h6, h901, h903, h921, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h923 | h923
                · linarith only [h14, h15, h923, hlam]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h925 | h925
                  · linarith only [h0, h10, h3, h7, h923, h925, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h927 | h927
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h928 | h928
                      · linarith only [h0, h13, h6, h901, h903, h928, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h930 | h930
                        · linarith only [h0, h3, h919, h927, h930, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h932 | h932
                          · linarith only [h14, h15, h921, h928, h932, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h934 | h934
                            · linarith only [h0, h14, h15, h3, h8, h930, h934, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h936 | h936
                              · linarith only [h0, h10, h14, h15, h3, h7, h925, h934, h936, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h938 | h938
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h939 | h939
                                  · linarith only [h0, h13, h3, h7, h901, h934, h938, h939, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h941 | h941
                                    · linarith only [h0, h10, h3, h7, h939, h941, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h943 | h943
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h944 | h944
                                        · rcases h6bigk with h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [hlam, p945_0]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            rcases p945_3 (m.d 0 6) (by simp) with h947 | h947
                                            · rcases p945_3 (m.d 1 6) (by simp) with h948 | h948
                                              · linarith only [h2, h948, hlam]
                                              · rcases p945_3 (m.d 2 6) (by simp) with h950 | h950
                                                · linarith only [h6, h950, hlam]
                                                · linarith only [h901, h950, hlam]
                                            · linarith only [h2, h947, hlam]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h0, h10, h12, h14, h3, h7, h901, h928, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h0, h10, h12, h14, h3, h7, h901, h928, h932, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h0, h10, h12, h13, h3, h7, h903, h941, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            rcases p945_3 (m.d 0 6) (by simp) with h957 | h957
                                            · rcases p945_3 (m.d 1 6) (by simp) with h958 | h958
                                              · linarith only [h2, h958, hlam]
                                              · linarith only [h927, h958, hlam]
                                            · linarith only [h12, h957, hlam]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h2, hlam, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [hlam, p945_0]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h901, hlam, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h921, hlam, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h925, hlam, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p945_1, u6ehi5]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h6, hlam, p945_0]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h0, h5, h938, hc01, hlam, hphi, ht0b, ht6b, p945_1, u6ehi1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [hlam, p945_0]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h932, hlam, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h936, hlam, p945_0]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h0, h10, h3, h7, h930, h938, h939, hc01, hlam, hphi, ht0b, ht6b, p945_1, u6ehi5]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h9, hlam, p945_0]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h0, h11, h14, h3, h7, h901, h928, h941, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h0, h11, h3, h7, h941, hc01, hlam, hphi, ht0b, ht6b, p945_1, u6ehi2]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [hlam, p945_0]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h941, hlam, p945_0]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h0, h10, h3, h7, h939, h943, hc01, hlam, hphi, ht0b, ht6b, p945_1, u6ehi5]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h11, hlam, p945_0]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h0, h11, h14, h3, h7, h901, h928, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h0, h11, h14, h3, h7, h901, h928, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p945_1, u6ehi3]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [hlam, p945_0]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h0, h10, h3, h7, h944, hc01, hlam, hphi, ht0b, ht6b, p945_1, u6ehi5]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h12, hlam, p945_0]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h927, hlam, p945_0]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h938, hlam, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h943, hlam, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [h944, hlam, p945_1]
                                          · obtain ⟨p945_0, p945_1, p945_2, p945_3⟩ := h945c
                                            linarith only [hlam, p945_0]
                                        · linarith only [h0, h10, h12, h14, h15, h3, h7, h928, h930, h939, h944, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                      · linarith only [h15, h927, h930, h943, hlam]
                                · linarith only [h15, h927, h938, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h995 | h995
                      · linarith only [h13, h903, h995, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h997 | h997
                        · linarith only [h0, h13, h6, h901, h997, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h999 | h999
                          · linarith only [h0, h10, h12, h14, h15, h3, h7, h927, h995, h999, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1001 | h1001
                            · linarith only [h0, h10, h1001, h12, h14, h15, h3, h7, h927, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1003 | h1003
                              · linarith only [h0, h10, h1003, h12, h14, h15, h3, h7, h927, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1005 | h1005
                                · linarith only [h1005, h14, h15, h927, h995, h997, hc23, hc35, hlam, hphi]
                                · linarith only [h0, h10, h1005, h12, h14, h15, h3, h7, h995, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1008 | h1008
      · rcases m.htr 1 2 6 (by decide) (by decide) with h1009 | h1009
        · linarith only [h0, h1009, h14, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1011 | h1011
          · linarith only [h1011, h13, h14, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1013 | h1013
            · rcases m.htr 1 3 6 (by decide) (by decide) with h1014 | h1014
              · linarith only [h0, h1014, h13, h14, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1016 | h1016
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1017 | h1017
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1018 | h1018
                    · linarith only [h0, h1013, h1018, h13, h14, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1020 | h1020
                      · linarith only [h0, h1011, h1013, h1020, h3, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1022 | h1022
                        · linarith only [h0, h1020, h1022, h13, h14, h3, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h1013, h1014, h1022, hc23, hc36, hlam, hphi]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1025 | h1025
                    · linarith only [h0, h1013, h1017, h1025, h11, h13, h14, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1027 | h1027
                      · linarith only [h0, h1017, h1027, h11, h13, h14, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1029 | h1029
                        · linarith only [h0, h1017, h1029, h11, h13, h14, h3, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h0, h1013, h1017, h1029, h11, h13, h14, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                · linarith only [h1013, h1016, h13, h14, hlam]
            · rcases m.htr 1 3 6 (by decide) (by decide) with h1033 | h1033
              · linarith only [h0, h1008, h1013, h1033, h14, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1035 | h1035
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1036 | h1036
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1037 | h1037
                    · linarith only [h0, h1008, h1037, h14, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1039 | h1039
                      · linarith only [h0, h1039, h13, h14, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1041 | h1041
                        · linarith only [h0, h1013, h1039, h1041, h13, h14, h3, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1043 | h1043
                          · linarith only [h0, h1033, h1039, h1043, h13, h14, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1045 | h1045
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1046 | h1046
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1047 | h1047
                                · linarith only [h0, h1008, h1009, h1039, h1046, h1047, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1049 | h1049
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1050 | h1050
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h1051 | h1051
                                      · linarith only [h1008, h1009, h1041, h1047, h1051, hc23, hc35, hlam, hphi]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h1053 | h1053
                                        · linarith only [h1008, h1009, h1043, h1045, h1051, h1053, hlam]
                                        · rcases h6bigk with h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            rcases p1055_3 (m.d 0 6) (by simp) with h1057 | h1057
                                            · rcases p1055_3 (m.d 1 6) (by simp) with h1058 | h1058
                                              · linarith only [h1058, h2, hlam]
                                              · rcases p1055_3 (m.d 2 6) (by simp) with h1060 | h1060
                                                · linarith only [h1060, h6, hlam]
                                                · linarith only [h1009, h1060, hlam]
                                            · linarith only [h1057, h2, hlam]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h0, h10, h1008, h1009, h1041, h12, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h0, h10, h1008, h1009, h1041, h1043, h12, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            rcases p1055_3 (m.d 0 6) (by simp) with h1066 | h1066
                                            · rcases p1055_3 (m.d 1 6) (by simp) with h1067 | h1067
                                              · linarith only [h1067, h2, hlam]
                                              · linarith only [h1036, h1067, hlam]
                                            · linarith only [h1066, h11, hlam]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h0, h10, h1013, h1051, h12, h3, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h2, hlam, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h1009, hlam, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h1033, hlam, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p1055_1, u6ehi4]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h1037, hlam, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h6, hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p1055_1, u6ehi1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h1043, hlam, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h0, h1039, h1046, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1055_1, u6ehi4]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h1047, hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h9, hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h0, h1008, h1009, h1041, h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p1055_1, u6ehi2]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h0, h1050, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1055_1, u6ehi4]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h1051, hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h11, hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h1036, hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h1046, hlam, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h1050, hlam, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h1053, hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h12, hlam, p1055_0]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h1008, h1009, h1041, hc23, hc56, hlam, hphi, ht34, ht45, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h0, h10, h1008, h1009, h1041, h12, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p1055_1]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1055_1, u6ehi3]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1055_1, u6ehi4]
                                          · obtain ⟨p1055_0, p1055_1, p1055_2, p1055_3⟩ := h1055c
                                            linarith only [hlam, p1055_0]
                                    · linarith only [h0, h1008, h1039, h1041, h1050, h11, h14, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                  · linarith only [h1008, h1009, h1039, h1045, h1046, h1049, hlam]
                              · linarith only [h1036, h1046, h14, hlam]
                            · linarith only [h0, h10, h1036, h1045, h14, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1106 | h1106
                    · linarith only [h0, h1008, h1009, h1106, h6, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1108 | h1108
                      · linarith only [h0, h1036, h11, h1108, h13, h14, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1110 | h1110
                        · linarith only [h0, h1013, h1036, h11, h1110, h13, h14, h3, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1112 | h1112
                          · linarith only [h0, h1036, h11, h1112, h13, h14, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1114 | h1114
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1115 | h1115
                              · linarith only [h0, h1008, h1036, h1108, h1110, h1115, h14, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                              · linarith only [h0, h1008, h11, h1110, h1115, h14, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                            · linarith only [h1008, h1110, h1114, h14, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1008, h1035, h14, hlam]
      · rcases m.htr 1 2 6 (by decide) (by decide) with h1120 | h1120
        · linarith only [h0, h1120, h14, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1122 | h1122
          · linarith only [h1122, h13, h14, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1124 | h1124
            · linarith only [h1008, h1124, h13, hlam]
            · rcases m.htr 1 3 6 (by decide) (by decide) with h1126 | h1126
              · linarith only [h0, h1126, h13, h14, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1128 | h1128
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1129 | h1129
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1130 | h1130
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1131 | h1131
                      · linarith only [h0, h1122, h1131, h13, h14, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1133 | h1133
                        · linarith only [h1, h1124, h1130, h1133, h13, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1135 | h1135
                          · linarith only [h0, h1126, h1131, h1135, h13, h14, h3, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1137 | h1137
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1138 | h1138
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1139 | h1139
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1140 | h1140
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1141 | h1141
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h1142 | h1142
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h1143 | h1143
                                        · linarith only [h0, h1128, h1131, h1143, h14, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                        · rcases h6bigk with h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [hlam, p1145_0]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            rcases p1145_3 (m.d 0 6) (by simp) with h1147 | h1147
                                            · rcases p1145_3 (m.d 1 6) (by simp) with h1148 | h1148
                                              · linarith only [h1148, h2, hlam]
                                              · rcases p1145_3 (m.d 2 6) (by simp) with h1150 | h1150
                                                · linarith only [h1150, h6, hlam]
                                                · linarith only [h1120, h1150, hlam]
                                            · linarith only [h1147, h2, hlam]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h0, h10, h1120, h12, h13, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h0, h10, h1120, h1135, h12, h13, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            rcases p1145_3 (m.d 0 6) (by simp) with h1156 | h1156
                                            · rcases p1145_3 (m.d 1 6) (by simp) with h1157 | h1157
                                              · linarith only [h1157, h2, hlam]
                                              · linarith only [h1129, h1157, hlam]
                                            · linarith only [h11, h1156, hlam]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            rcases p1145_3 (m.d 0 6) (by simp) with h1161 | h1161
                                            · rcases p1145_3 (m.d 1 6) (by simp) with h1162 | h1162
                                              · linarith only [h1162, h2, hlam]
                                              · linarith only [h1130, h1162, hlam]
                                            · linarith only [h1161, h12, hlam]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h2, hlam, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [hlam, p1145_0]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h1120, hlam, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h1126, hlam, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p1145_1, u6ehi4]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h1143, h2, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h6, hlam, p1145_0]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p1145_1, u6ehi1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [hlam, p1145_0]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h1135, hlam, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h0, h1131, h1138, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1145_1, u6ehi4]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h0, h1131, h1137, h1139, h1143, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h9, hlam, p1145_0]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h0, h1120, h13, h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p1145_1, u6ehi2]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [hlam, p1145_0]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h0, h1141, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1145_1, u6ehi4]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h0, h1142, h1143, h3, h8, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h11, hlam, p1145_0]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h1129, hlam, p1145_0]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h1138, hlam, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h1141, hlam, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [hlam, p1145_0]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h1143, hlam, p1145_0]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h12, hlam, p1145_0]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h1130, hlam, p1145_0]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h1139, hlam, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h1142, hlam, p1145_1]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [h1130, hc15, hlam, hphi, ht01, ht0b, ht6b, p1145_1, u6ehi4]
                                          · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                            linarith only [hlam, p1145_0]
                                      · linarith only [h1124, h1130, h1142, hlam]
                                    · linarith only [h1008, h11, h1130, h1131, h1137, h1141, h7, hc03, hlam, hphi, ht0b, ht6b, u6ehi5]
                                  · linarith only [h1120, h1131, h1137, h1139, h1140, h13, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h1008, h1128, h1130, h1139, h13, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                              · linarith only [h0, h11, h1138, h13, h14, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                            · linarith only [h1128, h1137, h14, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1202 | h1202
                      · linarith only [h0, h1202, h13, h14, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1204 | h1204
                        · linarith only [h0, h1204, h13, h14, h4, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1206 | h1206
                          · linarith only [h0, h10, h1008, h1130, h12, h1206, h13, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1208 | h1208
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1209 | h1209
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1210 | h1210
                                · linarith only [h1008, h1130, h1204, h1210, h13, hc23, hc35, hlam, hphi]
                                · linarith only [h0, h10, h1008, h12, h1210, h13, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                              · linarith only [h1129, h1209, h13, h14, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                            · linarith only [h1208, h13, h14, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1215 | h1215
                    · linarith only [h0, h11, h1128, h1129, h1215, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1217 | h1217
                      · linarith only [h0, h1217, h13, h14, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1219 | h1219
                        · linarith only [h0, h1219, h13, h14, h4, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1221 | h1221
                          · linarith only [h0, h1008, h11, h1128, h1129, h1221, h13, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1223 | h1223
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1224 | h1224
                              · linarith only [h0, h1008, h1128, h1129, h1217, h1224, h13, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                              · linarith only [h0, h11, h1224, h13, h14, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                            · linarith only [h1128, h1223, h13, h14, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1228 | h1228
                  · linarith only [h0, h10, h1128, h1228, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1230 | h1230
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1231 | h1231
                      · linarith only [h0, h1008, h1231, h13, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1233 | h1233
                        · linarith only [h0, h10, h1128, h1233, h13, h14, h3, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1235 | h1235
                          · linarith only [h0, h10, h1128, h1235, h13, h14, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1237 | h1237
                            · linarith only [h0, h1128, h1231, h1237, h13, h14, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                            · linarith only [h0, h10, h1237, h13, h14, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1240 | h1240
                      · linarith only [h1228, h1240, h13, h14, hc34, hc46, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1242 | h1242
                        · linarith only [h0, h10, h1128, h12, h1230, h1242, h13, h14, h3, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1244 | h1244
                          · linarith only [h0, h10, h1128, h12, h1230, h1244, h13, h14, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1246 | h1246
                            · linarith only [h0, h1128, h1240, h1246, h13, h14, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                            · linarith only [h0, h10, h1246, h13, h14, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1249 | h1249
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1250 | h1250
      · rcases m.htr 1 2 6 (by decide) (by decide) with h1251 | h1251
        · linarith only [h0, h1251, h13, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1253 | h1253
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1254 | h1254
            · rcases m.htr 1 3 6 (by decide) (by decide) with h1255 | h1255
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1256 | h1256
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1257 | h1257
                  · linarith only [h0, h1249, h1257, h13, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1259 | h1259
                    · linarith only [h0, h11, h1256, h1257, h1259, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1261 | h1261
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1262 | h1262
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1263 | h1263
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1264 | h1264
                            · linarith only [h0, h1249, h1251, h1263, h1264, h3, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · linarith only [h0, h11, h1256, h1257, h1264, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                          · linarith only [h1, h1250, h1255, h1262, h1263, h13, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h0, h1255, h1262, h13, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                      · linarith only [h0, h1250, h1261, h13, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1270 | h1270
                  · linarith only [h0, h1250, h1256, h1270, h13, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1272 | h1272
                    · linarith only [h0, h1250, h1272, h13, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1274 | h1274
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1275 | h1275
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1276 | h1276
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1277 | h1277
                            · linarith only [h0, h1249, h1251, h1256, h1276, h1277, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1279 | h1279
                              · linarith only [h0, h1249, h1251, h1270, h1276, h1279, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1281 | h1281
                                · linarith only [h0, h11, h1250, h1251, h1279, h1281, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1283 | h1283
                                  · linarith only [h1, h1253, h1256, h1283, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1285 | h1285
                                    · linarith only [h0, h10, h1249, h1256, h1274, h1285, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h1287 | h1287
                                      · linarith only [h1250, h1251, h1275, h1281, h1287, hlam]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h1289 | h1289
                                        · linarith only [h0, h10, h1250, h1251, h1275, h1281, h1283, h1289, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                        · rcases h6bigk with h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            rcases p1291_3 (m.d 0 6) (by simp) with h1293 | h1293
                                            · rcases p1291_3 (m.d 1 6) (by simp) with h1294 | h1294
                                              · linarith only [h1294, h2, hlam]
                                              · rcases p1291_3 (m.d 2 6) (by simp) with h1296 | h1296
                                                · linarith only [h1296, h6, hlam]
                                                · linarith only [h1251, h1296, hlam]
                                            · linarith only [h1293, h2, hlam]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h0, h10, h12, h1250, h1251, h1275, h1283, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p1291_1]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            rcases p1291_3 (m.d 0 6) (by simp) with h1301 | h1301
                                            · rcases p1291_3 (m.d 1 6) (by simp) with h1302 | h1302
                                              · linarith only [h1302, h2, hlam]
                                              · linarith only [h1255, h1302, hlam]
                                            · linarith only [h1301, h9, hlam]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h0, h10, h12, h1250, h1251, h1275, h1279, h1283, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p1291_1]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h0, h10, h12, h1256, h1289, h3, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p1291_1]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h2, hlam, p1291_1]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h1251, hlam, p1291_1]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p1291_1, u6ehi3]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h1270, hlam, p1291_1]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h1272, hlam, p1291_1]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h6, hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p1291_1, u6ehi1]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h0, h11, h1279, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1291_1, u6ehi3]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h1279, hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h1281, hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h9, hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h1255, hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h1276, hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h1285, hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h1287, hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h11, hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h0, h11, h1250, h1251, h1275, h1283, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p1291_1]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1291_1, u6ehi2]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1291_1, u6ehi3]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h1289, hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h12, hlam, p1291_0]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h1250, h1251, h1275, h1283, hc34, hc56, hlam, hphi, ht45, p1291_1]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h0, h10, h12, h1250, h1251, h1275, h1283, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p1291_1]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1291_1, u6ehi3]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1291_1, u6ehi4]
                                          · obtain ⟨p1291_0, p1291_1, p1291_2, p1291_3⟩ := h1291c
                                            linarith only [hlam, p1291_0]
                          · linarith only [h0, h1250, h1276, h13, h3, h9, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h0, h1249, h1274, h1275, h13, h3, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h1249, h1274, h13, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1341 | h1341
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1342 | h1342
                  · linarith only [h0, h1249, h13, h1342, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1344 | h1344
                    · linarith only [h0, h1249, h1255, h13, h1341, h1344, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1346 | h1346
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1347 | h1347
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1348 | h1348
                          · linarith only [h0, h1249, h1255, h13, h1346, h1348, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                          · linarith only [h0, h1249, h13, h1346, h1348, h3, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · linarith only [h0, h1249, h13, h1346, h1347, h3, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h1249, h13, h1346, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1353 | h1353
                  · linarith only [h0, h10, h1341, h1353, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1355 | h1355
                    · linarith only [h0, h1250, h1255, h13, h1355, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1357 | h1357
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1358 | h1358
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1359 | h1359
                          · linarith only [h0, h1249, h1255, h13, h1357, h1359, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                          · linarith only [h0, h1249, h13, h1357, h1359, h3, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · linarith only [h0, h1249, h13, h1357, h1358, h3, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h1249, h13, h1357, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
            · linarith only [h1250, h1254, h13, hlam]
          · linarith only [h1249, h1253, h13, hlam]
      · rcases m.htr 1 2 6 (by decide) (by decide) with h1366 | h1366
        · linarith only [h0, h1250, h1366, h5, hc01, hlam, hphi, ht0b, ht6b, u6ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1368 | h1368
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1369 | h1369
            · rcases m.htr 1 3 6 (by decide) (by decide) with h1370 | h1370
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1371 | h1371
                · linarith only [h1249, h1250, h1371, hlam]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1373 | h1373
                  · linarith only [h0, h10, h1371, h1373, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1375 | h1375
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1376 | h1376
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1377 | h1377
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1378 | h1378
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1379 | h1379
                            · linarith only [h0, h1249, h1250, h1371, h1377, h1379, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1381 | h1381
                              · linarith only [h0, h10, h1249, h1250, h1373, h1379, h1381, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1383 | h1383
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1384 | h1384
                                  · linarith only [h0, h1249, h1366, h1379, h1383, h1384, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1386 | h1386
                                    · linarith only [h1249, h1366, h1376, h1381, h1386, hlam]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h1388 | h1388
                                      · linarith only [h1, h1369, h1388, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h1390 | h1390
                                        · rcases h6bigk with h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            rcases p1391_3 (m.d 0 6) (by simp) with h1393 | h1393
                                            · rcases p1391_3 (m.d 1 6) (by simp) with h1394 | h1394
                                              · linarith only [h1394, h2, hlam]
                                              · rcases p1391_3 (m.d 2 6) (by simp) with h1396 | h1396
                                                · linarith only [h1396, h6, hlam]
                                                · linarith only [h1366, h1396, hlam]
                                            · linarith only [h1393, h2, hlam]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h0, h10, h12, h1249, h1366, h1376, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p1391_1]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            rcases p1391_3 (m.d 0 6) (by simp) with h1401 | h1401
                                            · rcases p1391_3 (m.d 1 6) (by simp) with h1402 | h1402
                                              · linarith only [h1402, h2, hlam]
                                              · linarith only [h1370, h1402, hlam]
                                            · linarith only [h1401, h9, hlam]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h0, h10, h12, h1249, h1366, h1376, h1381, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p1391_1]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            rcases p1391_3 (m.d 0 6) (by simp) with h1407 | h1407
                                            · rcases p1391_3 (m.d 1 6) (by simp) with h1408 | h1408
                                              · linarith only [h1408, h2, hlam]
                                              · linarith only [h1375, h1408, hlam]
                                            · linarith only [h12, h1407, hlam]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h2, hlam, p1391_1]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h1366, hlam, p1391_1]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p1391_1, u6ehi3]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h1373, hlam, p1391_1]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h1366, h1379, h1383, h1384, h1388, hc34, hc45, hlam, hphi, p1391_1]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h6, hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h0, h1383, h5, hc01, hlam, hphi, ht0b, ht6b, p1391_1, u6ehi1]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h0, h11, h1381, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1391_1, u6ehi3]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h1381, hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h0, h10, h1379, h1383, h1384, h1388, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p1391_1]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h9, hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h1370, hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h1378, hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h1386, hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h1388, hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h11, hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h0, h11, h1249, h1366, h1376, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p1391_1]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1391_1, u6ehi2]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1391_1, u6ehi3]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h0, h10, h1384, h1388, h1390, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p1391_1]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h12, hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h1375, hlam, p1391_0]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h1383, hlam, p1391_1]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h1375, hc15, hlam, hphi, ht01, ht0b, ht6b, p1391_1, u6ehi3]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [h1390, hlam, p1391_1]
                                          · obtain ⟨p1391_0, p1391_1, p1391_2, p1391_3⟩ := h1391c
                                            linarith only [hlam, p1391_0]
                                        · linarith only [h1250, h1375, h1379, h1390, hlam]
                                · linarith only [h1250, h1375, h1383, hlam]
                          · linarith only [h0, h1249, h13, h1376, h1378, h3, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · linarith only [h0, h13, h1369, h1375, h1377, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                      · linarith only [h0, h1249, h13, h1376, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1447 | h1447
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1448 | h1448
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1449 | h1449
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1450 | h1450
                            · linarith only [h0, h1249, h1250, h1448, h1450, h3, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1452 | h1452
                              · linarith only [h0, h10, h12, h1249, h1250, h1375, h1452, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1454 | h1454
                                · linarith only [h0, h10, h1249, h1250, h1375, h1450, h1454, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                · linarith only [h0, h10, h12, h1249, h1250, h1447, h1454, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                          · linarith only [h1249, h13, h1370, h1447, h1449, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                        · linarith only [h1249, h13, h1369, h1375, h1447, h1448, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h1249, h13, h1447, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1460 | h1460
                · linarith only [h1249, h1250, h1460, hlam]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1462 | h1462
                  · linarith only [h0, h1249, h13, h1462, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1464 | h1464
                    · linarith only [h0, h1369, h1370, h1464, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1466 | h1466
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1467 | h1467
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1468 | h1468
                          · linarith only [h0, h1369, h1370, h1468, h3, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                          · linarith only [h0, h1249, h13, h1468, h3, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · linarith only [h0, h1249, h13, h1466, h1467, h3, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h1249, h13, h1466, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
            · rcases m.htr 1 3 6 (by decide) (by decide) with h1473 | h1473
              · linarith only [h0, h1369, h1473, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1475 | h1475
                · linarith only [h1249, h1250, h1475, hlam]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1477 | h1477
                  · linarith only [h0, h1249, h13, h1369, h1477, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1479 | h1479
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1480 | h1480
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1481 | h1481
                        · linarith only [h0, h1249, h13, h1369, h1481, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · linarith only [h0, h1249, h13, h1480, h1481, h3, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h1249, h13, h1480, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1485 | h1485
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1486 | h1486
                        · linarith only [h0, h1249, h13, h1369, h1485, h1486, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · linarith only [h0, h1249, h13, h1485, h1486, h3, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h1249, h13, h1485, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
          · linarith only [h1249, h13, h1368, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1491 | h1491
      · rcases m.htr 1 2 6 (by decide) (by decide) with h1492 | h1492
        · linarith only [h0, h1249, h1492, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1494 | h1494
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1495 | h1495
            · rcases m.htr 1 3 6 (by decide) (by decide) with h1496 | h1496
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1497 | h1497
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1498 | h1498
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1499 | h1499
                    · linarith only [h0, h1249, h1491, h1499, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1501 | h1501
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1502 | h1502
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1503 | h1503
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1504 | h1504
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1505 | h1505
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1506 | h1506
                                · linarith only [h0, h1491, h1492, h1499, h1501, h1505, h1506, h3, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1508 | h1508
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1509 | h1509
                                    · linarith only [h1, h1494, h1509, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                                    · linarith only [h0, h1249, h1498, h1501, h1508, h1509, h3, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                  · linarith only [h0, h10, h12, h1491, h1492, h1504, h1506, h1508, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                              · linarith only [h1249, h1498, h1505, hlam]
                            · linarith only [h0, h10, h1249, h1498, h1504, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                          · linarith only [h0, h1249, h1491, h1501, h1503, h3, h9, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h0, h1249, h1491, h1501, h1502, h3, h8, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                      · linarith only [h0, h13, h1496, h1501, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1518 | h1518
                    · linarith only [h0, h1249, h1491, h1518, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1520 | h1520
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1521 | h1521
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1522 | h1522
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1523 | h1523
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1524 | h1524
                              · linarith only [h0, h1249, h1491, h1498, h1520, h1524, h3, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                              · linarith only [h0, h11, h1249, h1491, h1521, h1524, h3, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                            · linarith only [h0, h10, h1249, h1491, h1521, h1523, h3, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                          · linarith only [h13, h1491, h1496, h1521, h1522, hc13, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                        · linarith only [h0, h13, h1496, h1521, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                      · linarith only [h13, h1491, h1494, h1520, hc13, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b]
                · linarith only [h1249, h1491, h1497, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1532 | h1532
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1533 | h1533
                  · linarith only [h0, h1494, h1496, h1533, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1535 | h1535
                    · linarith only [h0, h13, h1491, h1535, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1537 | h1537
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1538 | h1538
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1539 | h1539
                          · linarith only [h0, h1249, h1491, h1494, h1496, h1539, h3, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                          · linarith only [h0, h13, h1491, h1538, h1539, h3, h9, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h0, h1249, h1491, h1537, h1538, h3, h8, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                      · linarith only [h0, h1494, h1496, h1537, h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                · linarith only [h1249, h1491, h1532, hlam]
            · linarith only [h13, h1491, h1495, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1546 | h1546
            · rcases m.htr 1 3 6 (by decide) (by decide) with h1547 | h1547
              · linarith only [h0, h1494, h1547, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1549 | h1549
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1550 | h1550
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1551 | h1551
                    · linarith only [h0, h13, h1491, h1551, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1553 | h1553
                      · linarith only [h0, h1494, h1546, h1553, h3, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                      · linarith only [h0, h13, h1491, h1553, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1556 | h1556
                    · linarith only [h0, h13, h1491, h1556, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1558 | h1558
                      · linarith only [h0, h13, h1491, h1494, h1558, h3, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                      · linarith only [h0, h13, h1491, h1558, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                · linarith only [h1249, h1491, h1549, hlam]
            · linarith only [h13, h1491, h1546, hlam]
      · rcases m.htr 1 2 6 (by decide) (by decide) with h1563 | h1563
        · linarith only [h0, h13, h1563, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1565 | h1565
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1566 | h1566
            · rcases m.htr 1 3 6 (by decide) (by decide) with h1567 | h1567
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1568 | h1568
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1569 | h1569
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1570 | h1570
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1571 | h1571
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1572 | h1572
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1573 | h1573
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1574 | h1574
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1575 | h1575
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1576 | h1576
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1577 | h1577
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1578 | h1578
                                    · linarith only [h1, h1565, h1578, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                                    · linarith only [h0, h1249, h1569, h1571, h1577, h1578, h3, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1581 | h1581
                                    · linarith only [h0, h10, h1577, h1581, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h1583 | h1583
                                      · linarith only [h0, h13, h1566, h1583, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h1585 | h1585
                                        · linarith only [h0, h1249, h1568, h1571, h1577, h1583, h1585, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                        · linarith only [h0, h1491, h1570, h1571, h1574, h1577, h1585, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                · linarith only [h1491, h1570, h1576, hlam]
                              · linarith only [h0, h11, h1491, h1570, h1574, h1575, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                            · linarith only [h1249, h1568, h1574, hlam]
                          · linarith only [h0, h1249, h1568, h1570, h1571, h1573, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                        · linarith only [h0, h1249, h1568, h1570, h1571, h1572, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                      · linarith only [h0, h13, h1565, h1568, h1570, h1571, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1594 | h1594
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1595 | h1595
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1596 | h1596
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1597 | h1597
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1598 | h1598
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1599 | h1599
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1600 | h1600
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1601 | h1601
                                    · linarith only [h1, h1565, h1601, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                                    · linarith only [h0, h1249, h1569, h1594, h1600, h1601, h3, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                  · linarith only [h0, h1568, h1570, h1594, h1597, h1599, h1600, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1605 | h1605
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1606 | h1606
                                    · linarith only [h0, h13, h1565, h1606, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                                    · linarith only [h0, h1249, h1569, h1594, h1605, h1606, h3, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1609 | h1609
                                    · linarith only [h0, h13, h1565, h1609, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h1611 | h1611
                                      · linarith only [h1491, h1568, h1599, h1605, h1611, hlam]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h1613 | h1613
                                        · linarith only [h1491, h1568, h1599, h1613, hlam]
                                        · rcases h6bigk with h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            rcases p1615_3 (m.d 0 6) (by simp) with h1617 | h1617
                                            · rcases p1615_3 (m.d 1 6) (by simp) with h1618 | h1618
                                              · linarith only [h1618, h2, hlam]
                                              · rcases p1615_3 (m.d 2 6) (by simp) with h1620 | h1620
                                                · linarith only [h1620, h6, hlam]
                                                · linarith only [h1563, h1620, hlam]
                                            · linarith only [h1617, h2, hlam]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            rcases p1615_3 (m.d 0 6) (by simp) with h1624 | h1624
                                            · rcases p1615_3 (m.d 1 6) (by simp) with h1625 | h1625
                                              · linarith only [h1625, h2, hlam]
                                              · rcases p1615_3 (m.d 2 6) (by simp) with h1627 | h1627
                                                · linarith only [h1627, h6, hlam]
                                                · rcases p1615_3 (m.d 3 6) (by simp) with h1629 | h1629
                                                  · linarith only [h1629, h9, hlam]
                                                  · rcases p1615_3 (m.d 4 6) (by simp) with h1631 | h1631
                                                    · linarith only [h11, h1631, hlam]
                                                    · rcases p1615_3 (m.d 5 6) (by simp) with h1633 | h1633
                                                      · linarith only [h12, h1633, hlam]
                                                      · linarith only [h1599, h1633, hlam]
                                            · linarith only [h1624, h6, hlam]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            rcases p1615_3 (m.d 0 6) (by simp) with h1637 | h1637
                                            · rcases p1615_3 (m.d 1 6) (by simp) with h1638 | h1638
                                              · linarith only [h1638, h2, hlam]
                                              · linarith only [h1567, h1638, hlam]
                                            · linarith only [h1637, h9, hlam]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            rcases p1615_3 (m.d 0 6) (by simp) with h1642 | h1642
                                            · rcases p1615_3 (m.d 1 6) (by simp) with h1643 | h1643
                                              · linarith only [h1643, h2, hlam]
                                              · linarith only [h1569, h1643, hlam]
                                            · linarith only [h11, h1642, hlam]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h0, h10, h12, h1491, h1599, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p1615_1]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h2, hlam, p1615_1]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h1563, hlam, p1615_1]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p1615_1, u6ehi3]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h0, h1249, h1569, h1594, h1609, h3, hc01, hlam, hphi, ht0b, ht6b, p1615_1, u6ehi3]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h1570, hlam, p1615_1]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h6, hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p1615_1, u6ehi1]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h0, h1596, h3, hc01, hlam, hphi, ht0b, ht6b, p1615_1, u6ehi3]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h0, h1594, h1598, h1609, h3, hc01, hlam, hphi, ht0b, ht6b, p1615_1, u6ehi3]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h1599, hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h9, hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h1567, hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h1596, hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h1609, hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h1611, hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h11, hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h1569, hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h1598, hlam, p1615_1]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1615_1, u6ehi3]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h1613, hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h12, hlam, p1615_0]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h0, h10, h12, h1569, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1615_1, u6ehi4]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1615_1, u6ehi2]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1615_1, u6ehi3]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [h0, h10, h12, h1609, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p1615_1]
                                          · obtain ⟨p1615_0, p1615_1, p1615_2, p1615_3⟩ := h1615c
                                            linarith only [hlam, p1615_0]
                              · linarith only [h1249, h1569, h1598, hlam]
                            · linarith only [h1249, h1568, h1597, hlam]
                          · linarith only [h0, h13, h1565, h1569, h1596, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                        · linarith only [h0, h13, h1565, h1569, h1595, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                      · linarith only [h0, h13, h1565, h1569, h1594, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1683 | h1683
                    · linarith only [h0, h11, h1568, h1569, h1683, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1685 | h1685
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1686 | h1686
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1687 | h1687
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1688 | h1688
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1689 | h1689
                              · linarith only [h0, h1568, h1569, h1689, h4, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1691 | h1691
                                · linarith only [h0, h11, h1683, h1688, h1689, h1691, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1693 | h1693
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1694 | h1694
                                    · linarith only [h1, h1565, h1689, h1694, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h1696 | h1696
                                      · linarith only [h1491, h1691, h1696, hc12, hc35, hlam, hphi, ht23]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h1698 | h1698
                                        · linarith only [h1491, h1691, h1698, hc12, hc45, hlam, hphi, ht23, ht34]
                                        · rcases h6bigk with h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            rcases p1700_3 (m.d 0 6) (by simp) with h1702 | h1702
                                            · rcases p1700_3 (m.d 1 6) (by simp) with h1703 | h1703
                                              · linarith only [h1703, h2, hlam]
                                              · rcases p1700_3 (m.d 2 6) (by simp) with h1705 | h1705
                                                · linarith only [h1705, h6, hlam]
                                                · linarith only [h1563, h1705, hlam]
                                            · linarith only [h1702, h2, hlam]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            rcases p1700_3 (m.d 0 6) (by simp) with h1709 | h1709
                                            · rcases p1700_3 (m.d 1 6) (by simp) with h1710 | h1710
                                              · linarith only [h1710, h2, hlam]
                                              · rcases p1700_3 (m.d 2 6) (by simp) with h1712 | h1712
                                                · linarith only [h1712, h6, hlam]
                                                · rcases p1700_3 (m.d 3 6) (by simp) with h1714 | h1714
                                                  · linarith only [h1714, h9, hlam]
                                                  · rcases p1700_3 (m.d 4 6) (by simp) with h1716 | h1716
                                                    · linarith only [h11, h1716, hlam]
                                                    · linarith only [h1689, h1716, hlam]
                                            · linarith only [h1709, h6, hlam]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            rcases p1700_3 (m.d 0 6) (by simp) with h1720 | h1720
                                            · rcases p1700_3 (m.d 1 6) (by simp) with h1721 | h1721
                                              · linarith only [h1721, h2, hlam]
                                              · linarith only [h1567, h1721, hlam]
                                            · linarith only [h1720, h9, hlam]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h0, h10, h12, h1565, h1569, h1693, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h0, h10, h12, h1491, h1691, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h2, hlam, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1563, hlam, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p1700_1, u6ehi3]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1569, hlam, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1683, hlam, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h6, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p1700_1, u6ehi1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h0, h1687, h3, hc01, hlam, hphi, ht0b, ht6b, p1700_1, u6ehi3]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1689, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1691, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h9, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1567, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1687, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1694, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1696, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h11, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h0, h11, h1565, h1569, h1693, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1700_1, u6ehi2]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1700_1, u6ehi3]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1698, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h12, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1565, h1569, h1693, hc45, hc56, hlam, hphi, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h0, h10, h12, h1491, h1688, h1689, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h0, h10, h12, h1693, h1694, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1700_1, u6ehi4]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [hlam, p1700_0]
                                  · linarith only [h0, h11, h1249, h1568, h1689, h1693, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                            · linarith only [h1249, h1568, h1688, hlam]
                          · linarith only [h13, h1567, h1687, hlam]
                        · linarith only [h13, h1566, h1686, hlam]
                      · linarith only [h0, h13, h1567, h1685, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h1762 | h1762
                  · linarith only [h0, h10, h1568, h1762, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h1764 | h1764
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1765 | h1765
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1766 | h1766
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1767 | h1767
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1768 | h1768
                            · linarith only [h0, h1568, h1764, h1768, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1770 | h1770
                              · linarith only [h0, h10, h1762, h1768, h1770, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1772 | h1772
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1773 | h1773
                                  · linarith only [h0, h1249, h1768, h1773, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1775 | h1775
                                    · linarith only [h1249, h1770, h1775, hc12, hc34, hlam, hphi, ht23]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h1777 | h1777
                                      · linarith only [h1, h1566, h1777, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h1779 | h1779
                                        · rcases h6bigk with h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            rcases p1780_3 (m.d 0 6) (by simp) with h1782 | h1782
                                            · rcases p1780_3 (m.d 1 6) (by simp) with h1783 | h1783
                                              · linarith only [h1783, h2, hlam]
                                              · rcases p1780_3 (m.d 2 6) (by simp) with h1785 | h1785
                                                · linarith only [h1785, h6, hlam]
                                                · linarith only [h1563, h1785, hlam]
                                            · linarith only [h1782, h2, hlam]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            rcases p1780_3 (m.d 0 6) (by simp) with h1789 | h1789
                                            · rcases p1780_3 (m.d 1 6) (by simp) with h1790 | h1790
                                              · linarith only [h1790, h2, hlam]
                                              · rcases p1780_3 (m.d 2 6) (by simp) with h1792 | h1792
                                                · linarith only [h1792, h6, hlam]
                                                · rcases p1780_3 (m.d 3 6) (by simp) with h1794 | h1794
                                                  · linarith only [h1794, h9, hlam]
                                                  · rcases p1780_3 (m.d 4 6) (by simp) with h1796 | h1796
                                                    · linarith only [h11, h1796, hlam]
                                                    · linarith only [h1770, h1796, hlam]
                                            · linarith only [h1789, h6, hlam]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            rcases p1780_3 (m.d 0 6) (by simp) with h1800 | h1800
                                            · rcases p1780_3 (m.d 1 6) (by simp) with h1801 | h1801
                                              · linarith only [h1801, h2, hlam]
                                              · linarith only [h1567, h1801, hlam]
                                            · linarith only [h1800, h9, hlam]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h0, h10, h12, h1249, h1770, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p1780_1]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            rcases p1780_3 (m.d 0 6) (by simp) with h1806 | h1806
                                            · rcases p1780_3 (m.d 1 6) (by simp) with h1807 | h1807
                                              · linarith only [h1807, h2, hlam]
                                              · linarith only [h1764, h1807, hlam]
                                            · linarith only [h12, h1806, hlam]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h2, hlam, p1780_1]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1563, hlam, p1780_1]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p1780_1, u6ehi3]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1762, hlam, p1780_1]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1491, h1764, h1768, h1773, h1777, hc34, hc45, hlam, hphi, p1780_1]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h6, hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p1780_1, u6ehi1]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h0, h1767, h3, hc01, hlam, hphi, ht0b, ht6b, p1780_1, u6ehi3]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1770, hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1770, h1773, h1777, hc34, hc46, hlam, hphi, p1780_1]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h9, hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1567, hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1767, hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1775, hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1777, hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h11, hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h0, h11, h1764, h1773, h1777, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p1780_1]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1780_1, u6ehi2]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1780_1, u6ehi3]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h0, h10, h1773, h1777, h1779, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p1780_1]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h12, hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1764, hlam, p1780_0]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1772, hlam, p1780_1]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1764, h2, hc01, hlam, hphi, ht0b, ht6b, p1780_1, u6ehi3]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [h1779, hlam, p1780_1]
                                          · obtain ⟨p1780_0, p1780_1, p1780_2, p1780_3⟩ := h1780c
                                            linarith only [hlam, p1780_0]
                                        · linarith only [h1491, h1764, h1768, h1779, hlam]
                                · linarith only [h1491, h1764, h1772, hlam]
                          · linarith only [h0, h13, h1566, h1764, h1767, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                        · linarith only [h0, h13, h1566, h1764, h1766, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                      · linarith only [h0, h13, h1566, h1764, h1765, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1846 | h1846
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1847 | h1847
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h1848 | h1848
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1849 | h1849
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1850 | h1850
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1851 | h1851
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1852 | h1852
                                  · linarith only [h1565, h1568, h1852, hlam]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1854 | h1854
                                    · linarith only [h1565, h1762, h1854, hlam]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h1856 | h1856
                                      · linarith only [h1566, h1764, h1856, hlam]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h1858 | h1858
                                        · linarith only [h0, h1764, h1846, h1849, h1858, h3, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b]
                                        · linarith only [h0, h1249, h1568, h1846, h1849, h1851, h1858, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1861 | h1861
                                  · linarith only [h1565, h1568, h1861, hlam]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1863 | h1863
                                    · linarith only [h1565, h1762, h1863, hlam]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h1865 | h1865
                                      · linarith only [h0, h1491, h1851, h1865, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h1867 | h1867
                                        · linarith only [h1849, h1851, h1867, hlam]
                                        · rcases h6bigk with h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            rcases p1869_3 (m.d 0 6) (by simp) with h1871 | h1871
                                            · rcases p1869_3 (m.d 1 6) (by simp) with h1872 | h1872
                                              · linarith only [h1872, h2, hlam]
                                              · rcases p1869_3 (m.d 2 6) (by simp) with h1874 | h1874
                                                · linarith only [h1874, h6, hlam]
                                                · linarith only [h1563, h1874, hlam]
                                            · linarith only [h1871, h2, hlam]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            rcases p1869_3 (m.d 0 6) (by simp) with h1878 | h1878
                                            · rcases p1869_3 (m.d 1 6) (by simp) with h1879 | h1879
                                              · linarith only [h1879, h2, hlam]
                                              · rcases p1869_3 (m.d 2 6) (by simp) with h1881 | h1881
                                                · linarith only [h1881, h6, hlam]
                                                · rcases p1869_3 (m.d 3 6) (by simp) with h1883 | h1883
                                                  · linarith only [h1883, h9, hlam]
                                                  · rcases p1869_3 (m.d 4 6) (by simp) with h1885 | h1885
                                                    · linarith only [h11, h1885, hlam]
                                                    · rcases p1869_3 (m.d 5 6) (by simp) with h1887 | h1887
                                                      · linarith only [h12, h1887, hlam]
                                                      · linarith only [h1851, h1887, hlam]
                                            · linarith only [h1878, h6, hlam]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            rcases p1869_3 (m.d 0 6) (by simp) with h1891 | h1891
                                            · rcases p1869_3 (m.d 1 6) (by simp) with h1892 | h1892
                                              · linarith only [h1892, h2, hlam]
                                              · linarith only [h1567, h1892, hlam]
                                            · linarith only [h1891, h9, hlam]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            rcases p1869_3 (m.d 0 6) (by simp) with h1896 | h1896
                                            · rcases p1869_3 (m.d 1 6) (by simp) with h1897 | h1897
                                              · linarith only [h1897, h2, hlam]
                                              · rcases p1869_3 (m.d 2 6) (by simp) with h1899 | h1899
                                                · linarith only [h1899, h6, hlam]
                                                · linarith only [h1850, h1899, hlam]
                                            · linarith only [h11, h1896, hlam]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h0, h10, h12, h1249, h1568, h1849, h1851, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p1869_1]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h2, hlam, p1869_1]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h1563, hlam, p1869_1]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p1869_1, u6ehi3]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h1762, hlam, p1869_1]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h1764, hlam, p1869_1]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h6, hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p1869_1, u6ehi1]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h0, h1848, h3, hc01, hlam, hphi, ht0b, ht6b, p1869_1, u6ehi3]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h0, h1846, h1850, h3, hc01, hlam, hphi, ht0b, ht6b, p1869_1, u6ehi4]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h1851, hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h9, hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h1567, hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h1848, hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h1863, hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h1865, hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h11, hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h0, h11, h1567, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1869_1, u6ehi3]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h1850, hlam, p1869_1]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h0, h1846, h1850, h3, hc01, hlam, hphi, ht0b, ht6b, p1869_1, u6ehi3]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h1867, hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h12, hlam, p1869_0]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h0, h10, h12, h1567, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1869_1, u6ehi3]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1869_1, u6ehi2]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1869_1, u6ehi3]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1869_1, u6ehi4]
                                          · obtain ⟨p1869_0, p1869_1, p1869_2, p1869_3⟩ := h1869c
                                            linarith only [hlam, p1869_0]
                              · linarith only [h0, h11, h1249, h1568, h1849, h1850, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h1935 | h1935
                              · linarith only [h0, h10, h1849, h1935, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h1937 | h1937
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1938 | h1938
                                  · linarith only [h1565, h1568, h1764, h1849, h1937, h1938, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h1940 | h1940
                                    · linarith only [h0, h10, h1249, h1565, h1568, h1764, h1849, h1935, h1937, h1940, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h1942 | h1942
                                      · linarith only [h0, h13, h1566, h1568, h1764, h1942, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h1944 | h1944
                                        · rcases h6bigk with h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            rcases p1945_3 (m.d 0 6) (by simp) with h1947 | h1947
                                            · rcases p1945_3 (m.d 1 6) (by simp) with h1948 | h1948
                                              · linarith only [h1948, h2, hlam]
                                              · rcases p1945_3 (m.d 2 6) (by simp) with h1950 | h1950
                                                · linarith only [h1950, h6, hlam]
                                                · linarith only [h1563, h1950, hlam]
                                            · linarith only [h1947, h2, hlam]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            rcases p1945_3 (m.d 0 6) (by simp) with h1954 | h1954
                                            · rcases p1945_3 (m.d 1 6) (by simp) with h1955 | h1955
                                              · linarith only [h1955, h2, hlam]
                                              · rcases p1945_3 (m.d 2 6) (by simp) with h1957 | h1957
                                                · linarith only [h1957, h6, hlam]
                                                · rcases p1945_3 (m.d 3 6) (by simp) with h1959 | h1959
                                                  · linarith only [h1959, h9, hlam]
                                                  · rcases p1945_3 (m.d 4 6) (by simp) with h1961 | h1961
                                                    · linarith only [h11, h1961, hlam]
                                                    · linarith only [h1935, h1961, hlam]
                                            · linarith only [h1954, h6, hlam]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            rcases p1945_3 (m.d 0 6) (by simp) with h1965 | h1965
                                            · rcases p1945_3 (m.d 1 6) (by simp) with h1966 | h1966
                                              · linarith only [h1966, h2, hlam]
                                              · linarith only [h1567, h1966, hlam]
                                            · linarith only [h1965, h9, hlam]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h0, h10, h12, h1249, h1935, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p1945_1]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            rcases p1945_3 (m.d 0 6) (by simp) with h1971 | h1971
                                            · rcases p1945_3 (m.d 1 6) (by simp) with h1972 | h1972
                                              · linarith only [h1972, h2, hlam]
                                              · rcases p1945_3 (m.d 2 6) (by simp) with h1974 | h1974
                                                · linarith only [h1974, h6, hlam]
                                                · linarith only [h1937, h1974, hlam]
                                            · linarith only [h12, h1971, hlam]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h2, hlam, p1945_1]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h1563, hlam, p1945_1]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p1945_1, u6ehi3]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h1762, hlam, p1945_1]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h1764, hlam, p1945_1]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h6, hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p1945_1, u6ehi1]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h0, h1848, h3, hc01, hlam, hphi, ht0b, ht6b, p1945_1, u6ehi3]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h1935, hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h0, h10, h1249, h1568, h1764, h1849, h1937, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p1945_1]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h9, hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h1567, hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h1848, hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h1940, hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h1942, hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h11, hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h0, h11, h1567, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1945_1, u6ehi3]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1945_1, u6ehi2]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1945_1, u6ehi3]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h0, h10, h1249, h1568, h1764, h1944, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p1945_1]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h12, hlam, p1945_0]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h0, h1567, h1937, h6, hc01, hlam, hphi, ht0b, ht6b, p1945_1, u6ehi3]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h1937, hlam, p1945_1]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h0, h10, h1849, h1937, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p1945_1, u6ehi3]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [h1944, hlam, p1945_1]
                                          · obtain ⟨p1945_0, p1945_1, p1945_2, p1945_3⟩ := h1945c
                                            linarith only [hlam, p1945_0]
                                        · linarith only [h1849, h1937, h1944, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2009 | h2009
                                  · linarith only [h1565, h1568, h2009, hlam]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2011 | h2011
                                    · linarith only [h0, h10, h1249, h1565, h1849, h1935, h2011, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi2]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2013 | h2013
                                      · linarith only [h1491, h1566, h1937, h2013, hlam]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h2015 | h2015
                                        · linarith only [h0, h10, h1249, h1849, h1937, h2015, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                        · linarith only [h1249, h1849, h2015, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                          · linarith only [h13, h1567, h1848, hlam]
                        · linarith only [h0, h13, h1567, h1847, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                      · linarith only [h13, h1565, h1846, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2021 | h2021
                · rcases m.htr 1 4 6 (by decide) (by decide) with h2022 | h2022
                  · linarith only [h0, h1565, h1567, h2022, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h2024 | h2024
                    · linarith only [h0, h1565, h1567, h2021, h2024, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2026 | h2026
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2027 | h2027
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2028 | h2028
                          · linarith only [h0, h1565, h1567, h2028, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2030 | h2030
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2031 | h2031
                              · linarith only [h0, h2022, h2026, h2028, h2031, h3, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2033 | h2033
                                · linarith only [h0, h2024, h2026, h2028, h2030, h2033, h3, h9, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2035 | h2035
                                  · linarith only [h0, h13, h1565, h2028, h2035, h3, h9, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                  · linarith only [h0, h1249, h2021, h2026, h2028, h2035, h3, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                            · linarith only [h1249, h2021, h2030, hlam]
                        · linarith only [h13, h1566, h2027, hlam]
                      · linarith only [h13, h1565, h2026, hlam]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h2041 | h2041
                  · linarith only [h0, h10, h2021, h2041, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h2043 | h2043
                    · linarith only [h0, h1566, h1567, h2043, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2045 | h2045
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2046 | h2046
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2047 | h2047
                          · linarith only [h0, h1565, h1567, h2047, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2049 | h2049
                            · linarith only [h0, h1249, h2021, h2045, h2047, h2049, h3, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2051 | h2051
                              · linarith only [h0, h1249, h2041, h2046, h2047, h2049, h2051, h3, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2053 | h2053
                                · linarith only [h0, h2046, h2047, h2053, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2055 | h2055
                                  · linarith only [h1, h1565, h2049, h2055, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2057 | h2057
                                    · linarith only [h1249, h1566, h2051, h2055, h2057, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2059 | h2059
                                      · linarith only [h0, h11, h13, h1566, h2047, h2057, h2059, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h2061 | h2061
                                        · linarith only [h13, h1566, h2047, h2055, h2059, h2061, hc34, hc45, hlam, hphi]
                                        · linarith only [h0, h10, h12, h1249, h2049, h2061, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                        · linarith only [h13, h1566, h2046, hlam]
                      · linarith only [h13, h1565, h2045, hlam]
            · rcases m.htr 1 3 6 (by decide) (by decide) with h2066 | h2066
              · linarith only [h0, h1566, h2066, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2068 | h2068
                · linarith only [h1565, h1566, h2068, hlam]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h2070 | h2070
                  · linarith only [h0, h1565, h1566, h2070, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h2072 | h2072
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2073 | h2073
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2074 | h2074
                        · linarith only [h0, h1565, h1566, h2074, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2076 | h2076
                          · linarith only [h0, h1565, h2066, h2074, h2076, h3, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2078 | h2078
                            · linarith only [h0, h2068, h2072, h2078, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2080 | h2080
                              · linarith only [h0, h2070, h2073, h2074, h2080, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2082 | h2082
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2083 | h2083
                                  · linarith only [h1, h1565, h2078, h2083, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2085 | h2085
                                    · linarith only [h0, h10, h1249, h13, h1565, h2074, h2080, h2083, h2085, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2087 | h2087
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h2088 | h2088
                                        · rcases h6bigk with h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [hlam, p2089_0]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            rcases p2089_3 (m.d 0 6) (by simp) with h2091 | h2091
                                            · rcases p2089_3 (m.d 1 6) (by simp) with h2092 | h2092
                                              · linarith only [h2, h2092, hlam]
                                              · rcases p2089_3 (m.d 2 6) (by simp) with h2094 | h2094
                                                · linarith only [h2094, h6, hlam]
                                                · linarith only [h1563, h2094, hlam]
                                            · linarith only [h2, h2091, hlam]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            rcases p2089_3 (m.d 0 6) (by simp) with h2098 | h2098
                                            · rcases p2089_3 (m.d 1 6) (by simp) with h2099 | h2099
                                              · linarith only [h2, h2099, hlam]
                                              · rcases p2089_3 (m.d 2 6) (by simp) with h2101 | h2101
                                                · linarith only [h2101, h6, hlam]
                                                · rcases p2089_3 (m.d 3 6) (by simp) with h2103 | h2103
                                                  · linarith only [h2103, h9, hlam]
                                                  · linarith only [h2076, h2103, hlam]
                                            · linarith only [h2098, h6, hlam]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h0, h10, h12, h1565, h2066, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h0, h10, h12, h1565, h2066, h2085, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            rcases p2089_3 (m.d 0 6) (by simp) with h2109 | h2109
                                            · rcases p2089_3 (m.d 1 6) (by simp) with h2110 | h2110
                                              · linarith only [h2, h2110, hlam]
                                              · linarith only [h2072, h2110, hlam]
                                            · linarith only [h12, h2109, hlam]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h2, hlam, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [hlam, p2089_0]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h1563, hlam, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h2066, hlam, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h2070, hlam, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p2089_1, u6ehi5]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h6, hlam, p2089_0]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p2089_1, u6ehi1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [hlam, p2089_0]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h2076, hlam, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h2080, hlam, p2089_0]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h0, h2082, h5, hc01, hlam, hphi, ht0b, ht6b, p2089_1, u6ehi5]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h9, hlam, p2089_0]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h0, h11, h1565, h2066, h2085, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h0, h11, h2085, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2089_1, u6ehi2]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [hlam, p2089_0]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h2085, hlam, p2089_0]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h0, h10, h2083, h2087, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2089_1, u6ehi5]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h11, hlam, p2089_0]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h0, h11, h1565, h2066, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h0, h11, h1249, h2073, h2076, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2089_1, u6ehi3]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [hlam, p2089_0]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h0, h10, h2088, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2089_1, u6ehi5]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h12, hlam, p2089_0]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h2072, hlam, p2089_0]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h2082, hlam, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h2087, hlam, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [h2088, hlam, p2089_1]
                                          · obtain ⟨p2089_0, p2089_1, p2089_2, p2089_3⟩ := h2089c
                                            linarith only [hlam, p2089_0]
                                        · linarith only [h0, h10, h12, h1565, h1566, h2083, h2088, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                      · linarith only [h1249, h2072, h2073, h2074, h2087, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                · linarith only [h1491, h2072, h2082, hlam]
                      · linarith only [h1, h13, h1565, h2073, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2148 | h2148
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2149 | h2149
                        · linarith only [h0, h1565, h1566, h2149, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2151 | h2151
                          · linarith only [h0, h2149, h2151, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2153 | h2153
                            · linarith only [h1249, h2068, h2148, h2151, h2153, hc12, hc36, hlam, hphi, ht23]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2155 | h2155
                              · linarith only [h0, h2148, h2151, h2155, h3, h9, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2157 | h2157
                                · linarith only [h0, h1565, h1566, h2072, h2157, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2159 | h2159
                                  · linarith only [h0, h10, h12, h13, h1565, h2149, h2157, h2159, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2161 | h2161
                                    · linarith only [h1249, h2155, h2161, hc12, hc34, hlam, hphi, ht23]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2163 | h2163
                                      · linarith only [h0, h10, h13, h1565, h2149, h2157, h2159, h2163, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                      · linarith only [h0, h10, h12, h1565, h1566, h2163, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h1565, h1566, h2148, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2167 | h2167
            · rcases m.htr 1 3 6 (by decide) (by decide) with h2168 | h2168
              · linarith only [h0, h1565, h2168, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2170 | h2170
                · rcases m.htr 1 4 6 (by decide) (by decide) with h2171 | h2171
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h2172 | h2172
                    · linarith only [h0, h1565, h2167, h2172, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2174 | h2174
                      · linarith only [h0, h1565, h2167, h2174, h3, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2176 | h2176
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2177 | h2177
                          · linarith only [h0, h2167, h2168, h2174, h2177, h3, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2179 | h2179
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2180 | h2180
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2181 | h2181
                                · linarith only [h0, h2172, h2174, h2176, h2181, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2183 | h2183
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2184 | h2184
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2185 | h2185
                                      · linarith only [h1, h2167, h2181, h2185, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h2187 | h2187
                                        · linarith only [h0, h10, h13, h2167, h2177, h2185, h2187, h3, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                        · rcases h6bigk with h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            rcases p2189_3 (m.d 0 6) (by simp) with h2191 | h2191
                                            · rcases p2189_3 (m.d 1 6) (by simp) with h2192 | h2192
                                              · linarith only [h2, h2192, hlam]
                                              · rcases p2189_3 (m.d 2 6) (by simp) with h2194 | h2194
                                                · linarith only [h2194, h6, hlam]
                                                · linarith only [h1563, h2194, hlam]
                                            · linarith only [h2, h2191, hlam]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            rcases p2189_3 (m.d 0 6) (by simp) with h2198 | h2198
                                            · rcases p2189_3 (m.d 1 6) (by simp) with h2199 | h2199
                                              · linarith only [h2, h2199, hlam]
                                              · rcases p2189_3 (m.d 2 6) (by simp) with h2201 | h2201
                                                · linarith only [h2201, h6, hlam]
                                                · rcases p2189_3 (m.d 3 6) (by simp) with h2203 | h2203
                                                  · linarith only [h2203, h9, hlam]
                                                  · linarith only [h2177, h2203, hlam]
                                            · linarith only [h2198, h6, hlam]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h0, h10, h12, h1491, h2176, h2177, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p2189_1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            rcases p2189_3 (m.d 0 6) (by simp) with h2208 | h2208
                                            · rcases p2189_3 (m.d 1 6) (by simp) with h2209 | h2209
                                              · linarith only [h2, h2209, hlam]
                                              · linarith only [h2171, h2209, hlam]
                                            · linarith only [h11, h2208, hlam]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h0, h10, h12, h1491, h2176, h2177, h2185, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p2189_1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h2, hlam, p2189_1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h1563, hlam, p2189_1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h2168, hlam, p2189_1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p2189_1, u6ehi4]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h2172, hlam, p2189_1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h6, hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p2189_1, u6ehi1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h2177, hlam, p2189_1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h0, h2180, h4, hc01, hlam, hphi, ht0b, ht6b, p2189_1, u6ehi4]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h2181, hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h9, hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h2167, h2168, h2183, h2185, hc45, hc56, hlam, hphi, p2189_1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p2189_1, u6ehi2]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h0, h2184, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2189_1, u6ehi4]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h2185, hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h11, hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h2171, hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h2180, hlam, p2189_1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h2184, hlam, p2189_1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h2187, hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h12, hlam, p2189_0]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h0, h10, h12, h2167, h2168, h2183, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p2189_1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h0, h10, h12, h1491, h2176, h2177, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p2189_1]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2189_1, u6ehi3]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2189_1, u6ehi4]
                                          · obtain ⟨p2189_0, p2189_1, p2189_2, p2189_3⟩ := h2189c
                                            linarith only [hlam, p2189_0]
                                    · linarith only [h0, h11, h1565, h2167, h2183, h2184, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                  · linarith only [h1491, h2174, h2176, h2183, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h1249, h2171, h2180, hlam]
                            · linarith only [h1249, h13, h2167, h2170, h2171, h2174, h2179, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi4]
                        · linarith only [h13, h2167, h2176, hlam]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h2249 | h2249
                    · linarith only [h0, h11, h1565, h2167, h2171, h2249, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2251 | h2251
                      · linarith only [h0, h1565, h2167, h2251, h3, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2253 | h2253
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2254 | h2254
                          · linarith only [h0, h2251, h2254, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2256 | h2256
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2257 | h2257
                              · linarith only [h0, h2170, h2171, h2251, h2257, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2259 | h2259
                                · linarith only [h0, h11, h2249, h2251, h2253, h2257, h2259, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2261 | h2261
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2262 | h2262
                                    · linarith only [h0, h1491, h2251, h2253, h2257, h2262, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                    · linarith only [h0, h11, h1565, h2167, h2261, h2262, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                  · linarith only [h1491, h2251, h2253, h2261, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h1491, h2, h2170, h2171, h2251, h2253, h2256, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                        · linarith only [h1, h13, h2167, h2253, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                · linarith only [h1565, h2167, h2170, hlam]
            · rcases m.htr 1 3 6 (by decide) (by decide) with h2269 | h2269
              · linarith only [h0, h2167, h2269, h3, h8, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2271 | h2271
                · rcases m.htr 1 4 6 (by decide) (by decide) with h2272 | h2272
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h2273 | h2273
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2274 | h2274
                      · linarith only [h0, h1565, h2272, h2274, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2276 | h2276
                        · linarith only [h2167, h2274, h2276, hc13, hc34, hlam, hphi]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2278 | h2278
                          · linarith only [h0, h2269, h2274, h2278, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2280 | h2280
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2281 | h2281
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2282 | h2282
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2283 | h2283
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2284 | h2284
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2285 | h2285
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h2286 | h2286
                                        · linarith only [h0, h1249, h2271, h2286, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                        · rcases h6bigk with h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [hlam, p2288_0]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            rcases p2288_3 (m.d 0 6) (by simp) with h2290 | h2290
                                            · rcases p2288_3 (m.d 1 6) (by simp) with h2291 | h2291
                                              · linarith only [h2, h2291, hlam]
                                              · rcases p2288_3 (m.d 2 6) (by simp) with h2293 | h2293
                                                · linarith only [h2293, h6, hlam]
                                                · linarith only [h1563, h2293, hlam]
                                            · linarith only [h2, h2290, hlam]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            rcases p2288_3 (m.d 0 6) (by simp) with h2297 | h2297
                                            · rcases p2288_3 (m.d 1 6) (by simp) with h2298 | h2298
                                              · linarith only [h2, h2298, hlam]
                                              · rcases p2288_3 (m.d 2 6) (by simp) with h2300 | h2300
                                                · linarith only [h2300, h6, hlam]
                                                · rcases p2288_3 (m.d 3 6) (by simp) with h2302 | h2302
                                                  · linarith only [h2302, h9, hlam]
                                                  · linarith only [h2278, h2302, hlam]
                                            · linarith only [h2297, h6, hlam]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h0, h10, h12, h13, h2278, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            rcases p2288_3 (m.d 0 6) (by simp) with h2307 | h2307
                                            · rcases p2288_3 (m.d 1 6) (by simp) with h2308 | h2308
                                              · linarith only [h2, h2308, hlam]
                                              · linarith only [h2272, h2308, hlam]
                                            · linarith only [h11, h2307, hlam]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            rcases p2288_3 (m.d 0 6) (by simp) with h2312 | h2312
                                            · rcases p2288_3 (m.d 1 6) (by simp) with h2313 | h2313
                                              · linarith only [h2, h2313, hlam]
                                              · linarith only [h2273, h2313, hlam]
                                            · linarith only [h12, h2312, hlam]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2, hlam, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [hlam, p2288_0]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h1563, hlam, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2269, hlam, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p2288_1, u6ehi4]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2, h2286, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h6, hlam, p2288_0]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p2288_1, u6ehi1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [hlam, p2288_0]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2278, hlam, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h0, h2274, h2281, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2288_1, u6ehi4]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h0, h2282, h2286, h5, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h9, hlam, p2288_0]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h0, h2273, h2286, h3, h9, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p2288_1, u6ehi2]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [hlam, p2288_0]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h0, h2284, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2288_1, u6ehi4]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h0, h2283, h2285, h2286, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h11, hlam, p2288_0]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2272, hlam, p2288_0]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2281, hlam, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2284, hlam, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [hlam, p2288_0]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2286, hlam, p2288_0]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h12, hlam, p2288_0]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2273, hlam, p2288_0]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2282, hlam, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2285, hlam, p2288_1]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [h2273, hc15, hlam, hphi, ht01, ht0b, ht6b, p2288_1, u6ehi4]
                                          · obtain ⟨p2288_0, p2288_1, p2288_2, p2288_3⟩ := h2288c
                                            linarith only [hlam, p2288_0]
                                      · linarith only [h1491, h2273, h2276, h2285, hlam]
                                    · linarith only [h0, h11, h1491, h2273, h2276, h2283, h2284, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                  · linarith only [h13, h2274, h2283, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1491, h2273, h2282, hlam]
                              · linarith only [h0, h11, h1249, h2271, h2273, h2281, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                            · linarith only [h1249, h2271, h2280, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2353 | h2353
                      · linarith only [h0, h1565, h2272, h2353, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2355 | h2355
                        · linarith only [h13, h2167, h2353, h2355, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2357 | h2357
                          · linarith only [h0, h2353, h2357, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2359 | h2359
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2360 | h2360
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2361 | h2361
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2362 | h2362
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2363 | h2363
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2364 | h2364
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h2365 | h2365
                                        · linarith only [h1249, h13, h2167, h2271, h2273, h2365, hc12, hc24, hlam, hphi]
                                        · rcases h6bigk with h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [hlam, p2367_0]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            rcases p2367_3 (m.d 0 6) (by simp) with h2369 | h2369
                                            · rcases p2367_3 (m.d 1 6) (by simp) with h2370 | h2370
                                              · linarith only [h2, h2370, hlam]
                                              · rcases p2367_3 (m.d 2 6) (by simp) with h2372 | h2372
                                                · linarith only [h2372, h6, hlam]
                                                · linarith only [h1563, h2372, hlam]
                                            · linarith only [h2, h2369, hlam]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            rcases p2367_3 (m.d 0 6) (by simp) with h2376 | h2376
                                            · rcases p2367_3 (m.d 1 6) (by simp) with h2377 | h2377
                                              · linarith only [h2, h2377, hlam]
                                              · rcases p2367_3 (m.d 2 6) (by simp) with h2379 | h2379
                                                · linarith only [h2379, h6, hlam]
                                                · rcases p2367_3 (m.d 3 6) (by simp) with h2381 | h2381
                                                  · linarith only [h2381, h9, hlam]
                                                  · linarith only [h2357, h2381, hlam]
                                            · linarith only [h2376, h6, hlam]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h0, h10, h12, h13, h2357, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p2367_1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            rcases p2367_3 (m.d 0 6) (by simp) with h2386 | h2386
                                            · rcases p2367_3 (m.d 1 6) (by simp) with h2387 | h2387
                                              · linarith only [h2, h2387, hlam]
                                              · linarith only [h2272, h2387, hlam]
                                            · linarith only [h11, h2386, hlam]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            rcases p2367_3 (m.d 0 6) (by simp) with h2391 | h2391
                                            · rcases p2367_3 (m.d 1 6) (by simp) with h2392 | h2392
                                              · linarith only [h2, h2392, hlam]
                                              · rcases p2367_3 (m.d 2 6) (by simp) with h2394 | h2394
                                                · linarith only [h2394, h6, hlam]
                                                · linarith only [h2361, h2394, hlam]
                                            · linarith only [h12, h2391, hlam]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h2, hlam, p2367_1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [hlam, p2367_0]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h1563, hlam, p2367_1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h2269, hlam, p2367_1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h2, hc01, hlam, hphi, ht0b, ht6b, p2367_1, u6ehi4]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h2273, hlam, p2367_1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h6, hlam, p2367_0]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p2367_1, u6ehi1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [hlam, p2367_0]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h2357, hlam, p2367_1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h0, h2353, h2360, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2367_1, u6ehi4]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h13, h2167, h2273, h2361, hc12, hc25, hlam, hphi, p2367_1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h9, hlam, p2367_0]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h0, h2272, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p2367_1, u6ehi4]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p2367_1, u6ehi2]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [hlam, p2367_0]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h0, h2363, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2367_1, u6ehi4]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h0, h13, h2167, h2273, h2362, h2364, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p2367_1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h11, hlam, p2367_0]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h2272, hlam, p2367_0]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h2360, hlam, p2367_1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h2363, hlam, p2367_1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [hlam, p2367_0]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h2365, hlam, p2367_0]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h12, hlam, p2367_0]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h0, h2272, h2361, h6, hc01, hlam, hphi, ht0b, ht6b, p2367_1, u6ehi4]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h2361, hlam, p2367_1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h2364, hlam, p2367_1]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [h0, h2355, h2361, h2362, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2367_1, u6ehi4]
                                          · obtain ⟨p2367_0, p2367_1, p2367_2, p2367_3⟩ := h2367c
                                            linarith only [hlam, p2367_0]
                                      · linarith only [h2355, h2361, h2364, hlam]
                                    · linarith only [h2, h2272, h2355, h2361, h2362, h2363, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                  · linarith only [h2271, h2273, h2353, h2359, h2361, h2362, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2431 | h2431
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2432 | h2432
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2433 | h2433
                                      · linarith only [h13, h2355, h2361, h2433, hc12, hc35, hlam, hphi, ht23]
                                      · linarith only [h13, h2355, h2433, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                                    · linarith only [h1249, h2272, h2353, h2432, hlam]
                                  · linarith only [h0, h1249, h1491, h2271, h2272, h2353, h2431, h5, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · linarith only [h1249, h2272, h2360, hlam]
                            · linarith only [h1249, h2271, h2359, hlam]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h2440 | h2440
                    · linarith only [h11, h2271, h2272, h2440, h7, hc03, hlam, hphi, ht0b, ht6b, u6ehi5]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2442 | h2442
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2443 | h2443
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2444 | h2444
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2445 | h2445
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2446 | h2446
                              · linarith only [h0, h2271, h2272, h2442, h2446, h3, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2448 | h2448
                                · linarith only [h0, h11, h13, h2167, h2440, h2445, h2446, h2448, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2450 | h2450
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2451 | h2451
                                    · linarith only [h0, h1249, h2446, h2451, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2453 | h2453
                                      · linarith only [h2443, h2448, h2453, hlam]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h2455 | h2455
                                        · linarith only [h13, h2167, h2271, h2443, h2448, h2455, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                        · rcases h6bigk with h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            rcases p2457_3 (m.d 0 6) (by simp) with h2459 | h2459
                                            · rcases p2457_3 (m.d 1 6) (by simp) with h2460 | h2460
                                              · linarith only [h2, h2460, hlam]
                                              · rcases p2457_3 (m.d 2 6) (by simp) with h2462 | h2462
                                                · linarith only [h2462, h6, hlam]
                                                · linarith only [h1563, h2462, hlam]
                                            · linarith only [h2, h2459, hlam]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            rcases p2457_3 (m.d 0 6) (by simp) with h2466 | h2466
                                            · rcases p2457_3 (m.d 1 6) (by simp) with h2467 | h2467
                                              · linarith only [h2, h2467, hlam]
                                              · rcases p2457_3 (m.d 2 6) (by simp) with h2469 | h2469
                                                · linarith only [h2469, h6, hlam]
                                                · rcases p2457_3 (m.d 3 6) (by simp) with h2471 | h2471
                                                  · linarith only [h2471, h9, hlam]
                                                  · rcases p2457_3 (m.d 4 6) (by simp) with h2473 | h2473
                                                    · linarith only [h11, h2473, hlam]
                                                    · linarith only [h2446, h2473, hlam]
                                            · linarith only [h2466, h6, hlam]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            rcases p2457_3 (m.d 0 6) (by simp) with h2477 | h2477
                                            · rcases p2457_3 (m.d 1 6) (by simp) with h2478 | h2478
                                              · linarith only [h2, h2478, hlam]
                                              · rcases p2457_3 (m.d 2 6) (by simp) with h2480 | h2480
                                                · linarith only [h2480, h6, hlam]
                                                · linarith only [h2444, h2480, hlam]
                                            · linarith only [h2477, h9, hlam]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h0, h10, h12, h13, h2167, h2443, h2445, h2446, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p2457_1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h0, h10, h12, h13, h2167, h2443, h2445, h2446, h2455, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p2457_1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h2, hlam, p2457_1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h1563, hlam, p2457_1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h2269, hlam, p2457_1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h2272, hlam, p2457_1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h2440, hlam, p2457_1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h6, hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p2457_1, u6ehi1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, p2457_1, u6ehi3]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h2446, hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h2448, hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h9, hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht6b, p2457_1, u6ehi1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h2444, hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h2451, hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h2453, hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h11, hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h0, h11, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2457_1, u6ehi1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h0, h10, h12, h2455, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2457_1, u6ehi2]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h0, h10, h12, h2269, h2455, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2457_1, u6ehi1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h2455, hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h12, hlam, p2457_0]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h0, h10, h12, h2271, h2272, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p2457_1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h0, h10, h12, h13, h2167, h2443, h2445, h2446, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p2457_1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h0, h10, h12, h13, h2167, h2450, h2451, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p2457_1]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [h0, h10, h12, h3, h7, hc01, hlam, hphi, ht0b, ht6b, p2457_1, u6ehi4]
                                          · obtain ⟨p2457_0, p2457_1, p2457_2, p2457_3⟩ := h2457c
                                            linarith only [hlam, p2457_0]
                                  · linarith only [h1249, h2271, h2446, h2450, hc34, hc46, hlam, hphi]
                            · linarith only [h1565, h2271, h2442, h2445, hlam]
                          · linarith only [h0, h13, h1565, h2442, h2444, h3, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                        · linarith only [h13, h1565, h2442, h2443, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2520 | h2520
                        · linarith only [h13, h2167, h2442, h2520, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2522 | h2522
                          · linarith only [h0, h2442, h2522, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2524 | h2524
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2525 | h2525
                              · linarith only [h0, h2271, h2272, h2525, h4, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2527 | h2527
                                · linarith only [h0, h11, h2524, h2525, h2527, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2529 | h2529
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2530 | h2530
                                    · linarith only [h0, h13, h2520, h2524, h2525, h2530, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                    · linarith only [h0, h11, h13, h2442, h2530, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                  · linarith only [h13, h2271, h2442, h2529, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b]
                            · linarith only [h0, h11, h2271, h2272, h2524, h3, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                · rcases m.htr 1 4 6 (by decide) (by decide) with h2535 | h2535
                  · linarith only [h0, h10, h2271, h2535, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h2537 | h2537
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2538 | h2538
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2539 | h2539
                        · linarith only [h0, h2167, h2537, h2539, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                        · linarith only [h0, h13, h1565, h2538, h2539, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2542 | h2542
                        · linarith only [h13, h2167, h2538, h2542, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2544 | h2544
                          · linarith only [h0, h2538, h2544, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2546 | h2546
                            · linarith only [h0, h2271, h2537, h2546, h4, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2548 | h2548
                              · linarith only [h0, h10, h2535, h2546, h2548, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi1]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2550 | h2550
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2551 | h2551
                                  · linarith only [h0, h13, h2538, h2546, h2551, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                  · linarith only [h0, h10, h13, h2538, h2551, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                · linarith only [h1491, h2537, h2550, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2555 | h2555
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2556 | h2556
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2557 | h2557
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2558 | h2558
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2559 | h2559
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2560 | h2560
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2561 | h2561
                                  · linarith only [h13, h1565, h2271, h2555, h2561, hc12, hc23, hlam, hphi]
                                  · linarith only [h0, h13, h1565, h2558, h2561, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2564 | h2564
                                  · linarith only [h0, h13, h1565, h2271, h2555, h2564, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                  · linarith only [h0, h13, h1565, h2555, h2558, h2564, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                              · linarith only [h0, h11, h13, h1565, h2271, h2558, h2559, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2568 | h2568
                              · linarith only [h0, h10, h2558, h2568, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2570 | h2570
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2571 | h2571
                                  · linarith only [h0, h1249, h2558, h2571, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2573 | h2573
                                    · linarith only [h2555, h2568, h2573, hlam]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2575 | h2575
                                      · linarith only [h0, h13, h1565, h2271, h2537, h2556, h2575, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                      · linarith only [h13, h2167, h2570, h2575, hc12, hc25, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2578 | h2578
                                  · linarith only [h13, h1565, h2271, h2555, h2568, h2578, hc12, hc46, hlam, hphi, ht23, ht34]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2580 | h2580
                                    · linarith only [h0, h10, h12, h2555, h2558, h2570, h2580, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2582 | h2582
                                      · linarith only [h0, h1249, h2558, h2570, h2582, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h2584 | h2584
                                        · linarith only [h13, h1565, h2555, h2558, h2570, h2584, hc12, hc45, hlam, hphi, ht23, ht34]
                                        · linarith only [h13, h1565, h2555, h2558, h2584, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                          · linarith only [h0, h13, h1565, h2555, h2557, h3, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                        · linarith only [h13, h1565, h2555, h2556, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2589 | h2589
                        · linarith only [h13, h2167, h2555, h2589, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 3 6 (by decide) (by decide) with h2591 | h2591
                          · linarith only [h0, h2555, h2591, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2593 | h2593
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2594 | h2594
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2595 | h2595
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2596 | h2596
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2597 | h2597
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2598 | h2598
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h2599 | h2599
                                        · linarith only [h13, h1565, h2271, h2537, h2593, h2599, hc12, hc24, hlam, hphi]
                                        · linarith only [h13, h1565, h2271, h2595, h2599, hc12, hc25, hlam, hphi]
                                      · linarith only [h2589, h2595, h2598, hlam]
                                    · linarith only [h2555, h2594, h2597, hlam]
                                  · linarith only [h0, h10, h2555, h2594, h2596, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2605 | h2605
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h2606 | h2606
                                    · rcases m.htr 3 5 6 (by decide) (by decide) with h2607 | h2607
                                      · linarith only [h0, h1491, h2595, h2607, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                      · linarith only [h0, h10, h12, h13, h2589, h2607, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                    · linarith only [h2555, h2594, h2606, hlam]
                                  · linarith only [h13, h1565, h2535, h2555, h2593, h2594, h2605, hc12, hc25, hlam, hphi]
                              · linarith only [h0, h11, h13, h1565, h2271, h2593, h2594, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                            · rcases m.htr 2 4 6 (by decide) (by decide) with h2613 | h2613
                              · linarith only [h0, h10, h2593, h2613, h3, h7, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                              · rcases m.htr 2 5 6 (by decide) (by decide) with h2615 | h2615
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2616 | h2616
                                  · linarith only [h0, h1249, h2593, h2616, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                                  · linarith only [h13, h2555, h2616, hc12, hc45, hlam, hphi, ht23, ht34]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2619 | h2619
                                  · linarith only [h13, h2555, h2593, h2619, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h13, h2555, h2619, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5222000 in
private theorem n8l_sBT8_H_R_M_IR_s11 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 6 ∧ m.d 0 1 < m.d 0 6 ∧ m.d 0 6 < m.d 1 6))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 6 ∧ m.d 0 2 < m.d 0 6 ∧ m.d 0 6 < m.d 2 6))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 3 + m.lam ≤ m.d 3 6 ∧ m.d 0 3 < m.d 0 6 ∧ m.d 0 6 < m.d 3 6))
    (hg10 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg11 : (m.d 0 4 + m.lam ≤ m.d 4 6 ∧ m.d 0 4 < m.d 0 6 ∧ m.d 0 6 < m.d 4 6))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h11 := hg11
  rcases m.htr 0 5 6 (by decide) (by decide) with h12 | h12
  · exact n8l_sBT8_H_R_M_IR_s12 m hb0 hb6 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  · linarith only [h12, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4]

set_option maxHeartbeats 5226000 in
private theorem n8l_sBT8_H_R_M_IR_s10 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 6 ∧ m.d 0 1 < m.d 0 6 ∧ m.d 0 6 < m.d 1 6))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 6 ∧ m.d 0 2 < m.d 0 6 ∧ m.d 0 6 < m.d 2 6))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 3 + m.lam ≤ m.d 3 6 ∧ m.d 0 3 < m.d 0 6 ∧ m.d 0 6 < m.d 3 6))
    (hg10 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  rcases m.htr 0 4 6 (by decide) (by decide) with h11 | h11
  · exact n8l_sBT8_H_R_M_IR_s11 m hb0 hb6 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  · linarith only [h11, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]

set_option maxHeartbeats 5230000 in
private theorem n8l_sBT8_H_R_M_IR_s9 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 6 ∧ m.d 0 1 < m.d 0 6 ∧ m.d 0 6 < m.d 1 6))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 6 ∧ m.d 0 2 < m.d 0 6 ∧ m.d 0 6 < m.d 2 6))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 3 + m.lam ≤ m.d 3 6 ∧ m.d 0 3 < m.d 0 6 ∧ m.d 0 6 < m.d 3 6))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 0 4 5 (by decide) (by decide) with h10 | h10
  · exact n8l_sBT8_H_R_M_IR_s10 m hb0 hb6 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · linarith only [h10, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]

set_option maxHeartbeats 5234000 in
private theorem n8l_sBT8_H_R_M_IR_s8 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 6 ∧ m.d 0 1 < m.d 0 6 ∧ m.d 0 6 < m.d 1 6))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 6 ∧ m.d 0 2 < m.d 0 6 ∧ m.d 0 6 < m.d 2 6))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 0 3 6 (by decide) (by decide) with h9 | h9
  · exact n8l_sBT8_H_R_M_IR_s9 m hb0 hb6 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  · linarith only [h9, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi2]

set_option maxHeartbeats 5238000 in
private theorem n8l_sBT8_H_R_M_IR_s7 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 6 ∧ m.d 0 1 < m.d 0 6 ∧ m.d 0 6 < m.d 1 6))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 6 ∧ m.d 0 2 < m.d 0 6 ∧ m.d 0 6 < m.d 2 6))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact n8l_sBT8_H_R_M_IR_s8 m hb0 hb6 h0 h1 h2 h3 h4 h5 h6 h7 h8
  · linarith only [h7, h8, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]

set_option maxHeartbeats 5242000 in
private theorem n8l_sBT8_H_R_M_IR_s6 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 6 ∧ m.d 0 1 < m.d 0 6 ∧ m.d 0 6 < m.d 1 6))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 6 ∧ m.d 0 2 < m.d 0 6 ∧ m.d 0 6 < m.d 2 6))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact n8l_sBT8_H_R_M_IR_s7 m hb0 hb6 h0 h1 h2 h3 h4 h5 h6 h7
  · linarith only [h7, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]

set_option maxHeartbeats 5246000 in
private theorem n8l_sBT8_H_R_M_IR_s5 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 6 ∧ m.d 0 1 < m.d 0 6 ∧ m.d 0 6 < m.d 1 6))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 2 6 (by decide) (by decide) with h6 | h6
  · exact n8l_sBT8_H_R_M_IR_s6 m hb0 hb6 h0 h1 h2 h3 h4 h5 h6
  · linarith only [h6, hc26, hlam, hphi, ht01, ht12, u0ehi1]

set_option maxHeartbeats 5250000 in
private theorem n8l_sBT8_H_R_M_IR_s4 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 6 ∧ m.d 0 1 < m.d 0 6 ∧ m.d 0 6 < m.d 1 6))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
  · exact n8l_sBT8_H_R_M_IR_s5 m hb0 hb6 h0 h1 h2 h3 h4 h5
  · linarith only [h3, h5, hc25, hlam, hphi, ht01, ht12, u0ehi2]

set_option maxHeartbeats 5254000 in
private theorem n8l_sBT8_H_R_M_IR_s3 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 6 ∧ m.d 0 1 < m.d 0 6 ∧ m.d 0 6 < m.d 1 6))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact n8l_sBT8_H_R_M_IR_s4 m hb0 hb6 h0 h1 h2 h3 h4
  · linarith only [h3, h4, hc24, hlam, hphi, ht01, ht12, u0ehi2]

set_option maxHeartbeats 5258000 in
private theorem n8l_sBT8_H_R_M_IR_s2 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 6 ∧ m.d 0 1 < m.d 0 6 ∧ m.d 0 6 < m.d 1 6))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact n8l_sBT8_H_R_M_IR_s3 m hb0 hb6 h0 h1 h2 h3
  · linarith only [h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]

set_option maxHeartbeats 5262000 in
private theorem n8l_sBT8_H_R_M_IR_s1 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 6 (by decide) (by decide) with h2 | h2
  · exact n8l_sBT8_H_R_M_IR_s2 m hb0 hb6 h0 h1 h2
  · linarith only [h2, hc16, hlam, hphi, ht01, u0ehi0]

set_option maxHeartbeats 5266000 in
private theorem n8l_sBT8_H_R_M_IR_s0 (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact n8l_sBT8_H_R_M_IR_s1 m hb0 hb6 h0 h1
  · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]

set_option maxHeartbeats 5270000 in
theorem n8l_sBT8_H_R_M_IR (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact n8l_sBT8_H_R_M_IR_s0 m hb0 hb6 h0
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

set_option maxHeartbeats 5526000 in
theorem n8l_sBT8_M_LI_H_I (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_I m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc06 := m.hcor 0 6 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h6bigk := hb6.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo5 := h0elo (m.d 0 6) (by simp)
  rcases h6bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h7 | h7
    · linarith only [h7, hlam, p0_0]
    · rcases p0_3 (m.d 1 6) (by simp) with h9 | h9
      · rcases p0_3 (m.d 2 6) (by simp) with h10 | h10
        · rcases p0_3 (m.d 3 6) (by simp) with h11 | h11
          · rcases p0_3 (m.d 4 6) (by simp) with h12 | h12
            · rcases p0_3 (m.d 5 6) (by simp) with h13 | h13
              · rcases m.htr 0 1 2 (by decide) (by decide) with h14 | h14
                · rcases m.htr 0 1 6 (by decide) (by decide) with h15 | h15
                  · linarith only [h15, hlam, p0_0]
                  · linarith only [h13, h15, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h18 | h18
                  · linarith only [h18, hlam, p0_0]
                  · linarith only [h13, h18, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h21 | h21
                · rcases m.htr 0 1 6 (by decide) (by decide) with h22 | h22
                  · linarith only [h22, hlam, p0_0]
                  · linarith only [h21, h22, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h25 | h25
                  · linarith only [h25, hlam, p0_0]
                  · linarith only [h12, h25, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h28 | h28
              · rcases m.htr 0 1 2 (by decide) (by decide) with h29 | h29
                · rcases m.htr 0 1 6 (by decide) (by decide) with h30 | h30
                  · linarith only [h30, hlam, p0_0]
                  · linarith only [h28, h29, h30, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h33 | h33
                  · linarith only [h33, hlam, p0_0]
                  · linarith only [h28, h33, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h36 | h36
                · rcases m.htr 0 1 6 (by decide) (by decide) with h37 | h37
                  · linarith only [h37, hlam, p0_0]
                  · linarith only [h36, h37, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h40 | h40
                  · linarith only [h40, hlam, p0_0]
                  · linarith only [h11, h40, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h43 | h43
            · rcases p0_3 (m.d 5 6) (by simp) with h44 | h44
              · rcases m.htr 0 1 2 (by decide) (by decide) with h45 | h45
                · rcases m.htr 0 1 6 (by decide) (by decide) with h46 | h46
                  · linarith only [h46, hlam, p0_0]
                  · linarith only [h44, h46, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h49 | h49
                  · linarith only [h49, hlam, p0_0]
                  · linarith only [h44, h49, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h52 | h52
                · rcases m.htr 0 1 6 (by decide) (by decide) with h53 | h53
                  · linarith only [h53, hlam, p0_0]
                  · linarith only [h52, h53, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h56 | h56
                  · linarith only [h56, hlam, p0_0]
                  · linarith only [h43, h56, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h59 | h59
              · rcases m.htr 0 1 2 (by decide) (by decide) with h60 | h60
                · rcases m.htr 0 1 6 (by decide) (by decide) with h61 | h61
                  · linarith only [h61, hlam, p0_0]
                  · linarith only [h59, h61, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h64 | h64
                  · linarith only [h64, hlam, p0_0]
                  · linarith only [h59, h64, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h67 | h67
                · rcases m.htr 0 1 6 (by decide) (by decide) with h68 | h68
                  · linarith only [h68, hlam, p0_0]
                  · linarith only [h67, h68, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h71 | h71
                  · linarith only [h71, hlam, p0_0]
                  · linarith only [h10, h71, hc01, hc26, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 6) (by simp) with h74 | h74
          · rcases p0_3 (m.d 4 6) (by simp) with h75 | h75
            · rcases p0_3 (m.d 5 6) (by simp) with h76 | h76
              · rcases m.htr 0 1 2 (by decide) (by decide) with h77 | h77
                · rcases m.htr 0 1 6 (by decide) (by decide) with h78 | h78
                  · linarith only [h78, hlam, p0_0]
                  · linarith only [h76, h78, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h81 | h81
                  · linarith only [h81, hlam, p0_0]
                  · linarith only [h76, h81, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h84 | h84
                · rcases m.htr 0 1 6 (by decide) (by decide) with h85 | h85
                  · linarith only [h85, hlam, p0_0]
                  · linarith only [h84, h85, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h88 | h88
                  · linarith only [h88, hlam, p0_0]
                  · linarith only [h75, h88, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h91 | h91
              · rcases m.htr 0 1 2 (by decide) (by decide) with h92 | h92
                · rcases m.htr 0 1 6 (by decide) (by decide) with h93 | h93
                  · linarith only [h93, hlam, p0_0]
                  · linarith only [h91, h92, h93, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h96 | h96
                  · linarith only [h96, hlam, p0_0]
                  · linarith only [h91, h96, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h99 | h99
                · rcases m.htr 0 1 6 (by decide) (by decide) with h100 | h100
                  · linarith only [h100, hlam, p0_0]
                  · linarith only [h100, h99, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h103 | h103
                  · linarith only [h103, hlam, p0_0]
                  · linarith only [h103, h74, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h106 | h106
            · rcases p0_3 (m.d 5 6) (by simp) with h107 | h107
              · rcases m.htr 0 1 2 (by decide) (by decide) with h108 | h108
                · rcases m.htr 0 1 6 (by decide) (by decide) with h109 | h109
                  · linarith only [h109, hlam, p0_0]
                  · linarith only [h107, h109, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h112 | h112
                  · linarith only [h112, hlam, p0_0]
                  · linarith only [h107, h112, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h115 | h115
                · rcases m.htr 0 1 6 (by decide) (by decide) with h116 | h116
                  · linarith only [h116, hlam, p0_0]
                  · linarith only [h115, h116, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h119 | h119
                  · linarith only [h119, hlam, p0_0]
                  · linarith only [h106, h119, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h122 | h122
              · rcases m.htr 0 1 2 (by decide) (by decide) with h123 | h123
                · rcases m.htr 0 1 6 (by decide) (by decide) with h124 | h124
                  · linarith only [h124, hlam, p0_0]
                  · linarith only [h122, h123, h124, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h127 | h127
                  · linarith only [h127, hlam, p0_0]
                  · linarith only [h122, h127, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h130 | h130
                · rcases m.htr 0 1 6 (by decide) (by decide) with h131 | h131
                  · linarith only [h131, hlam, p0_0]
                  · linarith only [h130, h131, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h134 | h134
                  · linarith only [h134, hlam, p0_0]
                  · linarith only [h134, hc01, hc16, hlam, hphi, p0_1]
      · linarith only [h9, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h139 | h139
    · linarith only [h139, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h141 | h141
      · rcases p0_3 (m.d 2 6) (by simp) with h142 | h142
        · linarith only [h142, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h144 | h144
          · rcases p0_3 (m.d 4 6) (by simp) with h145 | h145
            · rcases p0_3 (m.d 5 6) (by simp) with h146 | h146
              · rcases m.htr 0 1 2 (by decide) (by decide) with h147 | h147
                · rcases m.htr 0 1 6 (by decide) (by decide) with h148 | h148
                  · linarith only [h148, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h148, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h151 | h151
                  · linarith only [h139, h151, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h146, h151, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h154 | h154
                · rcases m.htr 0 1 6 (by decide) (by decide) with h155 | h155
                  · linarith only [h139, h155, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h155, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h158 | h158
                  · linarith only [h139, h154, h158, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h139, h158, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h161 | h161
              · rcases m.htr 0 1 2 (by decide) (by decide) with h162 | h162
                · rcases m.htr 0 1 6 (by decide) (by decide) with h163 | h163
                  · linarith only [h139, h163, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h161, h162, h163, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h166 | h166
                  · linarith only [h139, h166, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h161, h166, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h169 | h169
                · rcases m.htr 0 1 6 (by decide) (by decide) with h170 | h170
                  · linarith only [h139, h170, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h144, h170, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h173 | h173
                  · linarith only [h139, h173, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h144, h173, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h176 | h176
            · rcases p0_3 (m.d 5 6) (by simp) with h177 | h177
              · rcases m.htr 0 1 2 (by decide) (by decide) with h178 | h178
                · rcases m.htr 0 1 6 (by decide) (by decide) with h179 | h179
                  · linarith only [h139, h179, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h179, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h182 | h182
                  · linarith only [h139, h182, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h177, h182, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h185 | h185
                · rcases m.htr 0 1 6 (by decide) (by decide) with h186 | h186
                  · linarith only [h139, h186, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h186, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h189 | h189
                  · linarith only [h139, h189, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h176, h189, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h192 | h192
              · rcases m.htr 0 1 2 (by decide) (by decide) with h193 | h193
                · rcases m.htr 0 1 6 (by decide) (by decide) with h194 | h194
                  · linarith only [h139, h194, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h194, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h197 | h197
                  · linarith only [h139, h197, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h192, h197, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h200 | h200
                · rcases m.htr 0 1 6 (by decide) (by decide) with h201 | h201
                  · linarith only [h139, h201, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h201, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h204 | h204
                  · linarith only [h139, h204, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h139, h204, hc01, hc16, hlam, hphi, p0_1]
      · linarith only [h141, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h208 | h208
    · linarith only [h208, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h210 | h210
      · rcases p0_3 (m.d 2 6) (by simp) with h211 | h211
        · rcases p0_3 (m.d 3 6) (by simp) with h212 | h212
          · linarith only [h212, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h214 | h214
            · rcases p0_3 (m.d 5 6) (by simp) with h215 | h215
              · rcases m.htr 0 1 2 (by decide) (by decide) with h216 | h216
                · rcases m.htr 0 1 6 (by decide) (by decide) with h217 | h217
                  · linarith only [h217, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h208, h217, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h220 | h220
                  · linarith only [h208, h216, h220, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h208, h220, hc01, hc16, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h223 | h223
                · rcases m.htr 0 1 6 (by decide) (by decide) with h224 | h224
                  · linarith only [h208, h224, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h208, h224, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h227 | h227
                  · linarith only [h208, h223, h227, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h208, h227, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h230 | h230
              · rcases m.htr 0 1 2 (by decide) (by decide) with h231 | h231
                · rcases m.htr 0 1 6 (by decide) (by decide) with h232 | h232
                  · linarith only [h208, h232, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h208, h231, h232, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h235 | h235
                  · linarith only [h208, h235, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h208, h230, h235, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h238 | h238
                · rcases m.htr 0 1 6 (by decide) (by decide) with h239 | h239
                  · linarith only [h208, h239, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h208, h238, h239, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h242 | h242
                  · linarith only [h208, h238, h242, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h208, h211, h242, hc01, hc26, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 6) (by simp) with h245 | h245
          · linarith only [h245, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h247 | h247
            · rcases p0_3 (m.d 5 6) (by simp) with h248 | h248
              · rcases m.htr 0 1 2 (by decide) (by decide) with h249 | h249
                · rcases m.htr 0 1 6 (by decide) (by decide) with h250 | h250
                  · linarith only [h208, h250, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h208, h250, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h253 | h253
                  · linarith only [h208, h253, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h208, h248, h253, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h256 | h256
                · rcases m.htr 0 1 6 (by decide) (by decide) with h257 | h257
                  · linarith only [h208, h257, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h208, h247, h256, h257, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h260 | h260
                  · linarith only [h208, h256, h260, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h208, h247, h260, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h263 | h263
              · rcases m.htr 0 1 2 (by decide) (by decide) with h264 | h264
                · rcases m.htr 0 1 6 (by decide) (by decide) with h265 | h265
                  · linarith only [h208, h265, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h208, h263, h264, h265, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h268 | h268
                  · linarith only [h208, h264, h268, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h208, h263, h268, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h271 | h271
                · rcases m.htr 0 1 6 (by decide) (by decide) with h272 | h272
                  · linarith only [h208, h272, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h208, h271, h272, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h275 | h275
                  · linarith only [h208, h275, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h208, h275, hc01, hc16, hlam, hphi, p0_1]
      · linarith only [h210, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h279 | h279
    · linarith only [h279, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h281 | h281
      · rcases p0_3 (m.d 2 6) (by simp) with h282 | h282
        · rcases p0_3 (m.d 3 6) (by simp) with h283 | h283
          · rcases p0_3 (m.d 4 6) (by simp) with h284 | h284
            · linarith only [h284, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h286 | h286
              · rcases m.htr 0 1 2 (by decide) (by decide) with h287 | h287
                · rcases m.htr 0 1 6 (by decide) (by decide) with h288 | h288
                  · linarith only [h288, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h279, h287, h288, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h291 | h291
                  · linarith only [h279, h287, h291, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h279, h286, h291, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h294 | h294
                · rcases m.htr 0 1 6 (by decide) (by decide) with h295 | h295
                  · linarith only [h279, h295, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h279, h283, h295, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h298 | h298
                  · linarith only [h279, h294, h298, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h279, h298, hc01, hc16, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h301 | h301
            · linarith only [h301, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h303 | h303
              · rcases m.htr 0 1 2 (by decide) (by decide) with h304 | h304
                · rcases m.htr 0 1 6 (by decide) (by decide) with h305 | h305
                  · linarith only [h279, h305, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h279, h303, h304, h305, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h308 | h308
                  · linarith only [h279, h308, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h279, h303, h308, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h311 | h311
                · rcases m.htr 0 1 6 (by decide) (by decide) with h312 | h312
                  · linarith only [h279, h312, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h279, h311, h312, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h315 | h315
                  · linarith only [h279, h311, h315, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h279, h282, h315, hc01, hc26, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 6) (by simp) with h318 | h318
          · rcases p0_3 (m.d 4 6) (by simp) with h319 | h319
            · linarith only [h319, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h321 | h321
              · rcases m.htr 0 1 2 (by decide) (by decide) with h322 | h322
                · rcases m.htr 0 1 6 (by decide) (by decide) with h323 | h323
                  · linarith only [h279, h323, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h279, h321, h323, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h326 | h326
                  · linarith only [h279, h322, h326, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h279, h326, hc01, hc16, hlam, hphi, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h329 | h329
                · rcases m.htr 0 1 6 (by decide) (by decide) with h330 | h330
                  · linarith only [h279, h330, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h279, h318, h329, h330, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h333 | h333
                  · linarith only [h279, h329, h333, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h279, h333, hc01, hc16, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h336 | h336
            · linarith only [h336, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h338 | h338
              · rcases m.htr 0 1 2 (by decide) (by decide) with h339 | h339
                · rcases m.htr 0 1 6 (by decide) (by decide) with h340 | h340
                  · linarith only [h279, h340, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h279, h338, h340, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h343 | h343
                  · linarith only [h279, h339, h343, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h279, h338, h343, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h346 | h346
                · rcases m.htr 0 1 6 (by decide) (by decide) with h347 | h347
                  · linarith only [h279, h347, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h279, h347, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h350 | h350
                  · linarith only [h279, h346, h350, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h279, h350, hc01, hc16, hlam, hphi, p0_1]
      · linarith only [h281, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h354 | h354
    · linarith only [h354, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h356 | h356
      · rcases p0_3 (m.d 2 6) (by simp) with h357 | h357
        · rcases p0_3 (m.d 3 6) (by simp) with h358 | h358
          · rcases p0_3 (m.d 4 6) (by simp) with h359 | h359
            · rcases p0_3 (m.d 5 6) (by simp) with h360 | h360
              · linarith only [h360, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h362 | h362
                · rcases m.htr 0 1 6 (by decide) (by decide) with h363 | h363
                  · linarith only [h363, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h354, h362, h363, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h366 | h366
                  · linarith only [h354, h366, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h354, h359, h366, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h369 | h369
              · linarith only [h369, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h371 | h371
                · rcases m.htr 0 1 6 (by decide) (by decide) with h372 | h372
                  · linarith only [h354, h372, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h354, h358, h371, h372, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h375 | h375
                  · linarith only [h354, h371, h375, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h354, h358, h375, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h378 | h378
            · rcases p0_3 (m.d 5 6) (by simp) with h379 | h379
              · linarith only [h379, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h381 | h381
                · rcases m.htr 0 1 6 (by decide) (by decide) with h382 | h382
                  · linarith only [h354, h382, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h354, h378, h382, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h385 | h385
                  · linarith only [h354, h381, h385, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h354, h378, h385, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h388 | h388
              · linarith only [h388, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h390 | h390
                · rcases m.htr 0 1 6 (by decide) (by decide) with h391 | h391
                  · linarith only [h354, h391, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h354, h357, h391, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h394 | h394
                  · linarith only [h354, h390, h394, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h354, h357, h394, hc01, hc26, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 6) (by simp) with h397 | h397
          · rcases p0_3 (m.d 4 6) (by simp) with h398 | h398
            · rcases p0_3 (m.d 5 6) (by simp) with h399 | h399
              · linarith only [h399, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h401 | h401
                · rcases m.htr 0 1 6 (by decide) (by decide) with h402 | h402
                  · linarith only [h354, h402, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h354, h398, h402, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h405 | h405
                  · linarith only [h354, h401, h405, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h354, h398, h405, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h408 | h408
              · linarith only [h408, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h410 | h410
                · rcases m.htr 0 1 6 (by decide) (by decide) with h411 | h411
                  · linarith only [h354, h411, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h354, h397, h411, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h414 | h414
                  · linarith only [h354, h410, h414, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h354, h397, h414, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h417 | h417
            · rcases p0_3 (m.d 5 6) (by simp) with h418 | h418
              · linarith only [h418, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h420 | h420
                · rcases m.htr 0 1 6 (by decide) (by decide) with h421 | h421
                  · linarith only [h354, h421, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h354, h417, h421, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h424 | h424
                  · linarith only [h354, h420, h424, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h354, h417, h424, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h427 | h427
              · linarith only [h427, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h429 | h429
                · rcases m.htr 0 1 6 (by decide) (by decide) with h430 | h430
                  · linarith only [h354, h430, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h354, h429, h430, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h433 | h433
                  · linarith only [h354, h433, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h354, h433, hc01, hc16, hlam, hphi, p0_1]
      · linarith only [h356, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h437 | h437
    · linarith only [h437, hlam, p0_0]
    · rcases p0_3 (m.d 1 6) (by simp) with h439 | h439
      · rcases p0_3 (m.d 2 6) (by simp) with h440 | h440
        · rcases p0_3 (m.d 3 6) (by simp) with h441 | h441
          · rcases p0_3 (m.d 4 6) (by simp) with h442 | h442
            · rcases p0_3 (m.d 5 6) (by simp) with h443 | h443
              · rcases m.htr 0 1 2 (by decide) (by decide) with h444 | h444
                · rcases m.htr 0 1 6 (by decide) (by decide) with h445 | h445
                  · linarith only [h439, h445, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h444, h445, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h448 | h448
                  · linarith only [h439, h448, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h448, hc01, hc26, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h451 | h451
                · rcases m.htr 0 1 6 (by decide) (by decide) with h452 | h452
                  · linarith only [h439, h452, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h451, h452, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h455 | h455
                  · linarith only [h439, h455, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h455, hc01, hc26, hlam, hphi, ht12, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h458 | h458
              · rcases m.htr 0 1 2 (by decide) (by decide) with h459 | h459
                · rcases m.htr 0 1 6 (by decide) (by decide) with h460 | h460
                  · linarith only [h439, h460, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h459, h460, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h463 | h463
                  · linarith only [h439, h463, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h463, hc01, hc26, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h466 | h466
                · rcases m.htr 0 1 6 (by decide) (by decide) with h467 | h467
                  · linarith only [h439, h467, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h467, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h470 | h470
                  · linarith only [h439, h466, h470, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h470, hc01, hc26, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h473 | h473
            · rcases p0_3 (m.d 5 6) (by simp) with h474 | h474
              · rcases m.htr 0 1 2 (by decide) (by decide) with h475 | h475
                · rcases m.htr 0 1 6 (by decide) (by decide) with h476 | h476
                  · linarith only [h439, h476, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h475, h476, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h479 | h479
                  · linarith only [h439, h479, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h479, hc01, hc26, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h482 | h482
                · rcases m.htr 0 1 6 (by decide) (by decide) with h483 | h483
                  · linarith only [h439, h483, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h483, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h486 | h486
                  · linarith only [h439, h482, h486, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h486, hc01, hc26, hlam, hphi, ht12, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h489 | h489
              · rcases m.htr 0 1 2 (by decide) (by decide) with h490 | h490
                · rcases m.htr 0 1 6 (by decide) (by decide) with h491 | h491
                  · linarith only [h439, h491, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h490, h491, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h494 | h494
                  · linarith only [h439, h494, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h494, hc01, hc26, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h497 | h497
                · rcases m.htr 0 1 6 (by decide) (by decide) with h498 | h498
                  · linarith only [h439, h498, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h498, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h501 | h501
                  · linarith only [h439, h501, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h501, hc01, hc26, hlam, hphi, ht12, p0_1]
        · linarith only [h440, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h505 | h505
        · rcases p0_3 (m.d 3 6) (by simp) with h506 | h506
          · rcases p0_3 (m.d 4 6) (by simp) with h507 | h507
            · rcases p0_3 (m.d 5 6) (by simp) with h508 | h508
              · rcases m.htr 0 1 2 (by decide) (by decide) with h509 | h509
                · rcases m.htr 0 1 6 (by decide) (by decide) with h510 | h510
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h511 | h511
                    · linarith only [h511, hlam, p0_0]
                    · linarith only [h508, h511, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h439, h510, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h515 | h515
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h516 | h516
                    · linarith only [h516, hlam, p0_0]
                    · linarith only [h508, h509, h515, h516, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h439, h515, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h520 | h520
                · rcases m.htr 0 1 6 (by decide) (by decide) with h521 | h521
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h522 | h522
                    · linarith only [h522, hlam, p0_0]
                    · linarith only [h507, h522, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h439, h521, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h526 | h526
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h527 | h527
                    · linarith only [h527, hlam, p0_0]
                    · linarith only [h507, h520, h527, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · linarith only [h439, h526, hlam]
            · rcases p0_3 (m.d 5 6) (by simp) with h531 | h531
              · rcases m.htr 0 1 2 (by decide) (by decide) with h532 | h532
                · rcases m.htr 0 1 6 (by decide) (by decide) with h533 | h533
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h534 | h534
                    · linarith only [h534, hlam, p0_0]
                    · linarith only [h531, h534, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h439, h533, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h538 | h538
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h539 | h539
                    · linarith only [h539, hlam, p0_0]
                    · linarith only [h531, h532, h538, h539, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h439, h538, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h543 | h543
                · rcases m.htr 0 1 6 (by decide) (by decide) with h544 | h544
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h545 | h545
                    · linarith only [h545, hlam, p0_0]
                    · linarith only [h545, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h439, h544, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h549 | h549
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h550 | h550
                    · linarith only [h550, hlam, p0_0]
                    · linarith only [h506, h543, h549, h550, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                  · linarith only [h439, h549, hlam]
          · rcases p0_3 (m.d 4 6) (by simp) with h554 | h554
            · rcases p0_3 (m.d 5 6) (by simp) with h555 | h555
              · rcases m.htr 0 1 2 (by decide) (by decide) with h556 | h556
                · rcases m.htr 0 1 6 (by decide) (by decide) with h557 | h557
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h558 | h558
                    · linarith only [h558, hlam, p0_0]
                    · linarith only [h555, h558, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h439, h557, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h562 | h562
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h563 | h563
                    · linarith only [h563, hlam, p0_0]
                    · linarith only [h555, h556, h562, h563, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h439, h562, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h567 | h567
                · rcases m.htr 0 1 6 (by decide) (by decide) with h568 | h568
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h569 | h569
                    · linarith only [h569, hlam, p0_0]
                    · linarith only [h567, h569, hc12, hc26, hlam, hphi, p0_1]
                  · linarith only [h439, h568, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h573 | h573
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h574 | h574
                    · linarith only [h574, hlam, p0_0]
                    · linarith only [h554, h567, h574, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · linarith only [h439, h573, hlam]
            · rcases p0_3 (m.d 5 6) (by simp) with h578 | h578
              · rcases m.htr 0 1 2 (by decide) (by decide) with h579 | h579
                · rcases m.htr 0 1 6 (by decide) (by decide) with h580 | h580
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h581 | h581
                    · linarith only [h581, hlam, p0_0]
                    · linarith only [h578, h581, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h439, h580, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h585 | h585
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h586 | h586
                    · linarith only [h586, hlam, p0_0]
                    · linarith only [h578, h579, h585, h586, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h439, h585, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h590 | h590
                · rcases m.htr 0 1 6 (by decide) (by decide) with h591 | h591
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h592 | h592
                    · linarith only [h592, hlam, p0_0]
                    · linarith only [h592, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h439, h591, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h596 | h596
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h597 | h597
                    · linarith only [h597, hlam, p0_0]
                    · linarith only [h590, h596, h597, hc16, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1]
                  · linarith only [h439, h596, hlam]
        · linarith only [h505, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h602 | h602
    · linarith only [h602, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h604 | h604
      · linarith only [h604, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h606 | h606
        · rcases p0_3 (m.d 3 6) (by simp) with h607 | h607
          · rcases p0_3 (m.d 4 6) (by simp) with h608 | h608
            · rcases p0_3 (m.d 5 6) (by simp) with h609 | h609
              · rcases m.htr 0 1 2 (by decide) (by decide) with h610 | h610
                · rcases m.htr 0 1 6 (by decide) (by decide) with h611 | h611
                  · linarith only [h602, h611, hlam]
                  · linarith only [h610, h611, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h614 | h614
                  · linarith only [h602, h614, hlam]
                  · linarith only [h609, h614, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h617 | h617
                · rcases m.htr 0 1 6 (by decide) (by decide) with h618 | h618
                  · linarith only [h602, h618, hlam]
                  · linarith only [h617, h618, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h621 | h621
                  · linarith only [h602, h621, hlam]
                  · linarith only [h608, h621, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h624 | h624
              · rcases m.htr 0 1 2 (by decide) (by decide) with h625 | h625
                · rcases m.htr 0 1 6 (by decide) (by decide) with h626 | h626
                  · linarith only [h602, h626, hlam]
                  · linarith only [h624, h625, h626, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h629 | h629
                  · linarith only [h602, h629, hlam]
                  · linarith only [h624, h629, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h632 | h632
                · rcases m.htr 0 1 6 (by decide) (by decide) with h633 | h633
                  · linarith only [h602, h633, hlam]
                  · linarith only [h632, h633, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h636 | h636
                  · linarith only [h602, h636, hlam]
                  · linarith only [h607, h636, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h639 | h639
            · rcases p0_3 (m.d 5 6) (by simp) with h640 | h640
              · rcases m.htr 0 1 2 (by decide) (by decide) with h641 | h641
                · rcases m.htr 0 1 6 (by decide) (by decide) with h642 | h642
                  · linarith only [h602, h642, hlam]
                  · linarith only [h640, h641, h642, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h645 | h645
                  · linarith only [h602, h645, hlam]
                  · linarith only [h640, h645, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h648 | h648
                · rcases m.htr 0 1 6 (by decide) (by decide) with h649 | h649
                  · linarith only [h602, h649, hlam]
                  · linarith only [h648, h649, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h652 | h652
                  · linarith only [h602, h652, hlam]
                  · linarith only [h639, h652, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h655 | h655
              · rcases m.htr 0 1 2 (by decide) (by decide) with h656 | h656
                · rcases m.htr 0 1 6 (by decide) (by decide) with h657 | h657
                  · linarith only [h602, h657, hlam]
                  · linarith only [h655, h657, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h660 | h660
                  · linarith only [h602, h660, hlam]
                  · linarith only [h655, h660, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h663 | h663
                · rcases m.htr 0 1 6 (by decide) (by decide) with h664 | h664
                  · linarith only [h602, h664, hlam]
                  · linarith only [h663, h664, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h667 | h667
                  · linarith only [h602, h667, hlam]
                  · linarith only [h667, hc01, hc26, hlam, hphi, ht12, p0_1]
        · linarith only [h606, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h672 | h672
    · linarith only [h672, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h674 | h674
      · rcases p0_3 (m.d 2 6) (by simp) with h675 | h675
        · rcases p0_3 (m.d 3 6) (by simp) with h676 | h676
          · linarith only [h676, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h678 | h678
            · rcases p0_3 (m.d 5 6) (by simp) with h679 | h679
              · rcases m.htr 0 1 2 (by decide) (by decide) with h680 | h680
                · rcases m.htr 0 1 6 (by decide) (by decide) with h681 | h681
                  · linarith only [h674, h681, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h672, h681, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h684 | h684
                  · linarith only [h672, h674, h684, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h672, h684, hc01, hc26, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h687 | h687
                · rcases m.htr 0 1 6 (by decide) (by decide) with h688 | h688
                  · linarith only [h672, h674, h688, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h672, h688, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h691 | h691
                  · linarith only [h672, h674, h687, h691, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h672, h691, hc01, hc26, hlam, hphi, ht12, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h694 | h694
              · rcases m.htr 0 1 2 (by decide) (by decide) with h695 | h695
                · rcases m.htr 0 1 6 (by decide) (by decide) with h696 | h696
                  · linarith only [h672, h674, h696, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h672, h695, h696, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h699 | h699
                  · linarith only [h672, h674, h695, h699, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h672, h699, hc01, hc26, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h702 | h702
                · rcases m.htr 0 1 6 (by decide) (by decide) with h703 | h703
                  · linarith only [h672, h674, h703, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h672, h703, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h706 | h706
                  · linarith only [h672, h674, h702, h706, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h672, h706, hc01, hc26, hlam, hphi, ht12, p0_1]
        · linarith only [h675, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h710 | h710
        · rcases p0_3 (m.d 3 6) (by simp) with h711 | h711
          · linarith only [h711, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h713 | h713
            · rcases p0_3 (m.d 5 6) (by simp) with h714 | h714
              · rcases m.htr 0 1 2 (by decide) (by decide) with h715 | h715
                · rcases m.htr 0 1 6 (by decide) (by decide) with h716 | h716
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h717 | h717
                    · linarith only [h672, h715, h716, h717, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h672, h714, h717, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h674, h714, h716, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h721 | h721
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h722 | h722
                    · linarith only [h672, h721, h722, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h672, h714, h722, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h674, h714, h721, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h726 | h726
                · rcases m.htr 0 1 6 (by decide) (by decide) with h727 | h727
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h728 | h728
                    · linarith only [h672, h728, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h672, h728, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h674, h713, h726, h727, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h732 | h732
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h733 | h733
                    · linarith only [h672, h733, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h672, h713, h733, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h674, h713, h732, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h737 | h737
              · rcases m.htr 0 1 2 (by decide) (by decide) with h738 | h738
                · rcases m.htr 0 1 6 (by decide) (by decide) with h739 | h739
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h740 | h740
                    · linarith only [h672, h739, h740, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h672, h737, h740, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h674, h737, h738, h739, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h744 | h744
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h745 | h745
                    · linarith only [h672, h744, h745, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h672, h737, h745, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h674, h737, h744, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h749 | h749
                · rcases m.htr 0 1 6 (by decide) (by decide) with h750 | h750
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h751 | h751
                    · linarith only [h672, h750, h751, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h672, h751, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h674, h750, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h755 | h755
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h756 | h756
                    · linarith only [h672, h756, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h672, h756, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h674, h755, hc01, hc26, hlam, hphi, ht12, p0_1]
        · linarith only [h710, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h761 | h761
    · linarith only [h761, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h763 | h763
      · rcases p0_3 (m.d 2 6) (by simp) with h764 | h764
        · rcases p0_3 (m.d 3 6) (by simp) with h765 | h765
          · rcases p0_3 (m.d 4 6) (by simp) with h766 | h766
            · linarith only [h766, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h768 | h768
              · rcases m.htr 0 1 2 (by decide) (by decide) with h769 | h769
                · rcases m.htr 0 1 6 (by decide) (by decide) with h770 | h770
                  · linarith only [h763, h770, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h761, h770, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h773 | h773
                  · linarith only [h761, h763, h773, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h761, h773, hc01, hc26, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h776 | h776
                · rcases m.htr 0 1 6 (by decide) (by decide) with h777 | h777
                  · linarith only [h761, h763, h777, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h761, h776, h777, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h780 | h780
                  · linarith only [h761, h763, h776, h780, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h761, h780, hc01, hc26, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h783 | h783
            · linarith only [h783, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h785 | h785
              · rcases m.htr 0 1 2 (by decide) (by decide) with h786 | h786
                · rcases m.htr 0 1 6 (by decide) (by decide) with h787 | h787
                  · linarith only [h761, h763, h787, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h761, h787, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h790 | h790
                  · linarith only [h761, h763, h786, h790, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h761, h790, hc01, hc26, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h793 | h793
                · rcases m.htr 0 1 6 (by decide) (by decide) with h794 | h794
                  · linarith only [h761, h763, h794, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h761, h794, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h797 | h797
                  · linarith only [h761, h763, h793, h797, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h761, h797, hc01, hc26, hlam, hphi, ht12, p0_1]
        · linarith only [h764, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h801 | h801
        · rcases p0_3 (m.d 3 6) (by simp) with h802 | h802
          · rcases p0_3 (m.d 4 6) (by simp) with h803 | h803
            · linarith only [h803, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h805 | h805
              · rcases m.htr 0 1 2 (by decide) (by decide) with h806 | h806
                · rcases m.htr 0 1 6 (by decide) (by decide) with h807 | h807
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h808 | h808
                    · linarith only [h761, h806, h807, h808, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h761, h805, h808, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h763, h805, h807, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h812 | h812
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h813 | h813
                    · linarith only [h761, h812, h813, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h761, h805, h813, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h763, h805, h812, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h817 | h817
                · rcases m.htr 0 1 6 (by decide) (by decide) with h818 | h818
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h819 | h819
                    · linarith only [h761, h819, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h761, h819, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h763, h802, h817, h818, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h823 | h823
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h824 | h824
                    · linarith only [h761, h824, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h761, h802, h824, hc02, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h763, h802, h823, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h828 | h828
            · linarith only [h828, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h830 | h830
              · rcases m.htr 0 1 2 (by decide) (by decide) with h831 | h831
                · rcases m.htr 0 1 6 (by decide) (by decide) with h832 | h832
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h833 | h833
                    · linarith only [h761, h832, h833, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h761, h830, h833, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h763, h830, h832, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h837 | h837
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h838 | h838
                    · linarith only [h761, h837, h838, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h761, h830, h838, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h763, h830, h837, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h842 | h842
                · rcases m.htr 0 1 6 (by decide) (by decide) with h843 | h843
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h844 | h844
                    · linarith only [h761, h844, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h761, h844, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h763, h843, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h848 | h848
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h849 | h849
                    · linarith only [h761, h849, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h761, h849, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h763, h848, hc01, hc26, hlam, hphi, ht12, p0_1]
        · linarith only [h801, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h854 | h854
    · linarith only [h854, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h856 | h856
      · rcases p0_3 (m.d 2 6) (by simp) with h857 | h857
        · rcases p0_3 (m.d 3 6) (by simp) with h858 | h858
          · rcases p0_3 (m.d 4 6) (by simp) with h859 | h859
            · rcases p0_3 (m.d 5 6) (by simp) with h860 | h860
              · linarith only [h860, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h862 | h862
                · rcases m.htr 0 1 6 (by decide) (by decide) with h863 | h863
                  · linarith only [h856, h863, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h854, h863, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h866 | h866
                  · linarith only [h854, h856, h866, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h854, h866, hc01, hc26, hlam, hphi, ht12, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h869 | h869
              · linarith only [h869, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h871 | h871
                · rcases m.htr 0 1 6 (by decide) (by decide) with h872 | h872
                  · linarith only [h854, h856, h872, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h854, h871, h872, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h875 | h875
                  · linarith only [h854, h856, h871, h875, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h854, h875, hc01, hc26, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h878 | h878
            · rcases p0_3 (m.d 5 6) (by simp) with h879 | h879
              · linarith only [h879, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h881 | h881
                · rcases m.htr 0 1 6 (by decide) (by decide) with h882 | h882
                  · linarith only [h854, h856, h882, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h854, h881, h882, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h885 | h885
                  · linarith only [h854, h856, h881, h885, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h854, h885, hc01, hc26, hlam, hphi, ht12, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h888 | h888
              · linarith only [h888, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h890 | h890
                · rcases m.htr 0 1 6 (by decide) (by decide) with h891 | h891
                  · linarith only [h854, h856, h891, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h854, h891, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h894 | h894
                  · linarith only [h854, h856, h890, h894, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h854, h894, hc01, hc26, hlam, hphi, ht12, p0_1]
        · linarith only [h857, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h898 | h898
        · rcases p0_3 (m.d 3 6) (by simp) with h899 | h899
          · rcases p0_3 (m.d 4 6) (by simp) with h900 | h900
            · rcases p0_3 (m.d 5 6) (by simp) with h901 | h901
              · linarith only [h901, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h903 | h903
                · rcases m.htr 0 1 6 (by decide) (by decide) with h904 | h904
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h905 | h905
                    · linarith only [h854, h903, h905, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h854, h905, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h856, h900, h904, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h909 | h909
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h910 | h910
                    · linarith only [h854, h910, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h854, h900, h910, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h856, h900, h909, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h914 | h914
              · linarith only [h914, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h916 | h916
                · rcases m.htr 0 1 6 (by decide) (by decide) with h917 | h917
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h918 | h918
                    · linarith only [h854, h918, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h854, h918, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h856, h899, h917, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h922 | h922
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h923 | h923
                    · linarith only [h854, h923, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h854, h899, h923, hc02, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h856, h899, h922, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h927 | h927
            · rcases p0_3 (m.d 5 6) (by simp) with h928 | h928
              · linarith only [h928, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h930 | h930
                · rcases m.htr 0 1 6 (by decide) (by decide) with h931 | h931
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h932 | h932
                    · linarith only [h854, h932, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h854, h927, h932, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h856, h927, h931, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h936 | h936
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h937 | h937
                    · linarith only [h854, h937, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h854, h927, h937, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h856, h927, h936, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h941 | h941
              · linarith only [h941, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h943 | h943
                · rcases m.htr 0 1 6 (by decide) (by decide) with h944 | h944
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h945 | h945
                    · linarith only [h854, h945, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h854, h945, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h856, h944, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h949 | h949
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h950 | h950
                    · linarith only [h854, h950, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h854, h950, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h856, h949, hc01, hc26, hlam, hphi, ht12, p0_1]
        · linarith only [h898, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h955 | h955
    · linarith only [h955, hlam, p0_0]
    · rcases p0_3 (m.d 1 6) (by simp) with h957 | h957
      · rcases p0_3 (m.d 2 6) (by simp) with h958 | h958
        · rcases p0_3 (m.d 3 6) (by simp) with h959 | h959
          · rcases p0_3 (m.d 4 6) (by simp) with h960 | h960
            · rcases p0_3 (m.d 5 6) (by simp) with h961 | h961
              · rcases m.htr 0 1 2 (by decide) (by decide) with h962 | h962
                · rcases m.htr 0 1 6 (by decide) (by decide) with h963 | h963
                  · linarith only [h957, h963, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h963, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h966 | h966
                  · linarith only [h957, h966, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h966, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h969 | h969
                · rcases m.htr 0 1 6 (by decide) (by decide) with h970 | h970
                  · linarith only [h957, h970, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h970, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h973 | h973
                  · linarith only [h957, h973, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h973, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h976 | h976
              · rcases m.htr 0 1 2 (by decide) (by decide) with h977 | h977
                · rcases m.htr 0 1 6 (by decide) (by decide) with h978 | h978
                  · linarith only [h957, h978, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h978, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h981 | h981
                  · linarith only [h957, h981, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h981, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h984 | h984
                · rcases m.htr 0 1 6 (by decide) (by decide) with h985 | h985
                  · linarith only [h957, h985, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h984, h985, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h988 | h988
                  · linarith only [h957, h984, h988, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h988, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h959, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h992 | h992
          · rcases p0_3 (m.d 4 6) (by simp) with h993 | h993
            · rcases p0_3 (m.d 5 6) (by simp) with h994 | h994
              · rcases m.htr 0 1 2 (by decide) (by decide) with h995 | h995
                · rcases m.htr 0 1 6 (by decide) (by decide) with h996 | h996
                  · linarith only [h957, h996, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h996, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h999 | h999
                  · linarith only [h957, h999, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h999, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1002 | h1002
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1003 | h1003
                  · linarith only [h1003, h957, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1003, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1006 | h1006
                  · linarith only [h1006, h957, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1006, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1009 | h1009
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1010 | h1010
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1011 | h1011
                  · linarith only [h1011, h957, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1011, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1014 | h1014
                  · linarith only [h1014, h957, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1014, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1017 | h1017
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1018 | h1018
                  · linarith only [h1018, h957, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1017, h1018, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1021 | h1021
                  · linarith only [h1017, h1021, h957, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1021, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h992, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1025 | h1025
        · rcases p0_3 (m.d 3 6) (by simp) with h1026 | h1026
          · rcases p0_3 (m.d 4 6) (by simp) with h1027 | h1027
            · rcases p0_3 (m.d 5 6) (by simp) with h1028 | h1028
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1029 | h1029
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1030 | h1030
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1031 | h1031
                    · linarith only [h1025, h1029, h1030, h1031, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1028, h1031, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h1030, h957, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1035 | h1035
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1036 | h1036
                    · linarith only [h1025, h1035, h1036, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1028, h1036, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h1035, h957, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1040 | h1040
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1041 | h1041
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1042 | h1042
                    · linarith only [h1025, h1042, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1042, hc02, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h1041, h957, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1046 | h1046
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1047 | h1047
                    · linarith only [h1025, h1047, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1040, h1047, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · linarith only [h1046, h957, hlam]
            · rcases p0_3 (m.d 5 6) (by simp) with h1051 | h1051
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1052 | h1052
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1053 | h1053
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1054 | h1054
                    · linarith only [h1025, h1053, h1054, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1051, h1054, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h1053, h957, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1058 | h1058
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1059 | h1059
                    · linarith only [h1025, h1058, h1059, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1051, h1059, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h1058, h957, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1063 | h1063
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1064 | h1064
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1065 | h1065
                    · linarith only [h1025, h1065, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1025, h1065, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h1064, h957, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1069 | h1069
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1070 | h1070
                    · linarith only [h1025, h1070, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1070, hc02, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h1069, h957, hlam]
          · linarith only [h1026, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1075 | h1075
          · rcases p0_3 (m.d 4 6) (by simp) with h1076 | h1076
            · rcases p0_3 (m.d 5 6) (by simp) with h1077 | h1077
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1078 | h1078
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1079 | h1079
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1080 | h1080
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1081 | h1081
                      · linarith only [h1081, hlam, p0_0]
                      · linarith only [h1077, h1081, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h1025, h1080, hlam]
                  · linarith only [h1079, h957, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1086 | h1086
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1087 | h1087
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1088 | h1088
                      · linarith only [h1088, hlam, p0_0]
                      · linarith only [h1077, h1088, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h1025, h1087, hlam]
                  · linarith only [h1086, h957, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1093 | h1093
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1094 | h1094
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1095 | h1095
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1096 | h1096
                      · linarith only [h1096, hlam, p0_0]
                      · linarith only [h1076, h1096, hc03, hc46, hlam, hphi, ht34, p0_1]
                    · linarith only [h1025, h1095, hlam]
                  · linarith only [h1094, h957, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1101 | h1101
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1102 | h1102
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1103 | h1103
                      · linarith only [h1103, hlam, p0_0]
                      · linarith only [h1076, h1103, hc03, hc46, hlam, hphi, ht34, p0_1]
                    · linarith only [h1025, h1102, hlam]
                  · linarith only [h1101, h957, hlam]
            · rcases p0_3 (m.d 5 6) (by simp) with h1108 | h1108
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1109 | h1109
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1110 | h1110
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1111 | h1111
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1112 | h1112
                      · linarith only [h1112, hlam, p0_0]
                      · linarith only [h1108, h1112, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h1025, h1111, hlam]
                  · linarith only [h1110, h957, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1117 | h1117
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1118 | h1118
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1119 | h1119
                      · linarith only [h1119, hlam, p0_0]
                      · linarith only [h1108, h1119, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h1025, h1118, hlam]
                  · linarith only [h1117, h957, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1124 | h1124
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1125 | h1125
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1126 | h1126
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1127 | h1127
                      · linarith only [h1127, hlam, p0_0]
                      · linarith only [h1127, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1025, h1126, hlam]
                  · linarith only [h1125, h957, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1132 | h1132
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1133 | h1133
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1134 | h1134
                      · linarith only [h1134, hlam, p0_0]
                      · linarith only [h1134, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1025, h1133, hlam]
                  · linarith only [h1132, h957, hlam]
          · linarith only [h1075, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1140 | h1140
    · linarith only [h1140, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h1142 | h1142
      · linarith only [h1142, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1144 | h1144
        · rcases p0_3 (m.d 3 6) (by simp) with h1145 | h1145
          · rcases p0_3 (m.d 4 6) (by simp) with h1146 | h1146
            · rcases p0_3 (m.d 5 6) (by simp) with h1147 | h1147
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1148 | h1148
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1149 | h1149
                  · linarith only [h1140, h1149, hlam]
                  · linarith only [h1147, h1149, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1152 | h1152
                  · linarith only [h1140, h1152, hlam]
                  · linarith only [h1147, h1152, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1155 | h1155
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1156 | h1156
                  · linarith only [h1140, h1156, hlam]
                  · linarith only [h1144, h1155, h1156, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1159 | h1159
                  · linarith only [h1140, h1159, hlam]
                  · linarith only [h1146, h1159, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1162 | h1162
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1163 | h1163
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1164 | h1164
                  · linarith only [h1140, h1164, hlam]
                  · linarith only [h1162, h1163, h1164, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1167 | h1167
                  · linarith only [h1140, h1167, hlam]
                  · linarith only [h1162, h1167, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1170 | h1170
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1171 | h1171
                  · linarith only [h1140, h1171, hlam]
                  · linarith only [h1170, h1171, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1174 | h1174
                  · linarith only [h1140, h1174, hlam]
                  · linarith only [h1174, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1145, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1178 | h1178
          · rcases p0_3 (m.d 4 6) (by simp) with h1179 | h1179
            · rcases p0_3 (m.d 5 6) (by simp) with h1180 | h1180
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1181 | h1181
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1182 | h1182
                  · linarith only [h1140, h1182, hlam]
                  · linarith only [h1180, h1181, h1182, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1185 | h1185
                  · linarith only [h1140, h1185, hlam]
                  · linarith only [h1180, h1185, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1188 | h1188
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1189 | h1189
                  · linarith only [h1140, h1189, hlam]
                  · linarith only [h1188, h1189, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1192 | h1192
                  · linarith only [h1140, h1192, hlam]
                  · linarith only [h1179, h1192, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1195 | h1195
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1196 | h1196
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1197 | h1197
                  · linarith only [h1140, h1197, hlam]
                  · linarith only [h1195, h1196, h1197, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1200 | h1200
                  · linarith only [h1140, h1200, hlam]
                  · linarith only [h1195, h1200, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1203 | h1203
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1204 | h1204
                  · linarith only [h1140, h1204, hlam]
                  · linarith only [h1203, h1204, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1207 | h1207
                  · linarith only [h1140, h1207, hlam]
                  · linarith only [h1207, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1178, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1211 | h1211
    · linarith only [h1211, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h1213 | h1213
      · rcases p0_3 (m.d 2 6) (by simp) with h1214 | h1214
        · linarith only [h1214, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1216 | h1216
          · rcases p0_3 (m.d 4 6) (by simp) with h1217 | h1217
            · rcases p0_3 (m.d 5 6) (by simp) with h1218 | h1218
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1219 | h1219
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1220 | h1220
                  · linarith only [h1213, h1220, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1211, h1220, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1223 | h1223
                  · linarith only [h1211, h1213, h1223, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1211, h1223, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1226 | h1226
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1227 | h1227
                  · linarith only [h1211, h1213, h1227, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1211, h1227, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1230 | h1230
                  · linarith only [h1211, h1213, h1230, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1211, h1230, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1233 | h1233
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1234 | h1234
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1235 | h1235
                  · linarith only [h1211, h1213, h1235, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1211, h1235, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1238 | h1238
                  · linarith only [h1211, h1213, h1238, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1211, h1238, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1241 | h1241
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1242 | h1242
                  · linarith only [h1211, h1213, h1242, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1211, h1242, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1245 | h1245
                  · linarith only [h1211, h1213, h1245, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1211, h1245, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1216, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1249 | h1249
        · linarith only [h1249, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1251 | h1251
          · rcases p0_3 (m.d 4 6) (by simp) with h1252 | h1252
            · rcases p0_3 (m.d 5 6) (by simp) with h1253 | h1253
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1254 | h1254
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1255 | h1255
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1256 | h1256
                    · linarith only [h1211, h1256, hlam]
                    · linarith only [h1253, h1256, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h1213, h1253, h1254, h1255, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1260 | h1260
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1261 | h1261
                    · linarith only [h1211, h1261, hlam]
                    · linarith only [h1253, h1254, h1261, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · linarith only [h1213, h1253, h1260, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1265 | h1265
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1266 | h1266
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1267 | h1267
                    · linarith only [h1211, h1267, hlam]
                    · linarith only [h1267, hc02, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h1213, h1252, h1265, h1266, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1271 | h1271
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1272 | h1272
                    · linarith only [h1211, h1272, hlam]
                    · linarith only [h1252, h1265, h1271, h1272, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                  · linarith only [h1213, h1252, h1271, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1276 | h1276
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1277 | h1277
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1278 | h1278
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1279 | h1279
                    · linarith only [h1211, h1279, hlam]
                    · linarith only [h1276, h1279, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h1213, h1276, h1277, h1278, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1283 | h1283
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1284 | h1284
                    · linarith only [h1211, h1284, hlam]
                    · linarith only [h1276, h1277, h1283, h1284, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h1213, h1276, h1283, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1288 | h1288
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1289 | h1289
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1290 | h1290
                    · linarith only [h1211, h1290, hlam]
                    · linarith only [h1288, h1290, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h1213, h1288, h1289, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1294 | h1294
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1295 | h1295
                    · linarith only [h1211, h1295, hlam]
                    · linarith only [h1288, h1294, h1295, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                  · linarith only [h1213, h1294, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1251, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1301 | h1301
    · linarith only [h1301, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h1303 | h1303
      · rcases p0_3 (m.d 2 6) (by simp) with h1304 | h1304
        · rcases p0_3 (m.d 3 6) (by simp) with h1305 | h1305
          · rcases p0_3 (m.d 4 6) (by simp) with h1306 | h1306
            · linarith only [h1306, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1308 | h1308
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1309 | h1309
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1310 | h1310
                  · linarith only [h1303, h1310, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1301, h1304, h1310, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1313 | h1313
                  · linarith only [h1301, h1303, h1313, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1301, h1313, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1316 | h1316
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1317 | h1317
                  · linarith only [h1301, h1303, h1317, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1301, h1316, h1317, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1320 | h1320
                  · linarith only [h1301, h1303, h1320, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1301, h1320, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1305, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1324 | h1324
          · rcases p0_3 (m.d 4 6) (by simp) with h1325 | h1325
            · linarith only [h1325, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1327 | h1327
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1328 | h1328
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1329 | h1329
                  · linarith only [h1301, h1303, h1329, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1301, h1329, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1332 | h1332
                  · linarith only [h1301, h1303, h1328, h1332, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1301, h1332, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1335 | h1335
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1336 | h1336
                  · linarith only [h1301, h1303, h1336, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1301, h1336, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1339 | h1339
                  · linarith only [h1301, h1303, h1339, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1301, h1339, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1324, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1343 | h1343
        · rcases p0_3 (m.d 3 6) (by simp) with h1344 | h1344
          · rcases p0_3 (m.d 4 6) (by simp) with h1345 | h1345
            · linarith only [h1345, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1347 | h1347
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1348 | h1348
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1349 | h1349
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1350 | h1350
                    · linarith only [h1301, h1343, h1349, h1350, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1301, h1347, h1350, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h1303, h1347, h1348, h1349, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1354 | h1354
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1355 | h1355
                    · linarith only [h1301, h1343, h1354, h1355, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1301, h1347, h1355, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h1303, h1347, h1354, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1359 | h1359
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1360 | h1360
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1361 | h1361
                    · linarith only [h1301, h1343, h1361, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1301, h1343, h1361, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h1303, h1359, h1360, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1365 | h1365
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1366 | h1366
                    · linarith only [h1301, h1343, h1366, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1301, h1366, hc02, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h1303, h1365, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1344, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1371 | h1371
          · rcases p0_3 (m.d 4 6) (by simp) with h1372 | h1372
            · linarith only [h1372, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1374 | h1374
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1375 | h1375
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1376 | h1376
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1377 | h1377
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1378 | h1378
                      · linarith only [h1301, h1378, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1301, h1378, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1343, h1374, h1377, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h1303, h1374, h1375, h1376, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1383 | h1383
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1384 | h1384
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1385 | h1385
                      · linarith only [h1301, h1385, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1301, h1385, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1343, h1374, h1375, h1383, h1384, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h1303, h1374, h1383, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1390 | h1390
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1391 | h1391
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1392 | h1392
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1393 | h1393
                      · linarith only [h1301, h1393, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1301, h1393, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1343, h1392, hc02, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h1303, h1390, h1391, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1398 | h1398
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1399 | h1399
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1400 | h1400
                      · linarith only [h1301, h1400, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1301, h1400, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1343, h1390, h1399, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · linarith only [h1303, h1398, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1371, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1406 | h1406
    · linarith only [h1406, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h1408 | h1408
      · rcases p0_3 (m.d 2 6) (by simp) with h1409 | h1409
        · rcases p0_3 (m.d 3 6) (by simp) with h1410 | h1410
          · rcases p0_3 (m.d 4 6) (by simp) with h1411 | h1411
            · rcases p0_3 (m.d 5 6) (by simp) with h1412 | h1412
              · linarith only [h1412, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1414 | h1414
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1415 | h1415
                  · linarith only [h1408, h1415, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1406, h1409, h1415, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1418 | h1418
                  · linarith only [h1406, h1408, h1418, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1406, h1418, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1421 | h1421
              · linarith only [h1421, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1423 | h1423
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1424 | h1424
                  · linarith only [h1406, h1408, h1424, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1406, h1424, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1427 | h1427
                  · linarith only [h1406, h1408, h1427, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1406, h1427, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1410, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1431 | h1431
          · rcases p0_3 (m.d 4 6) (by simp) with h1432 | h1432
            · rcases p0_3 (m.d 5 6) (by simp) with h1433 | h1433
              · linarith only [h1433, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1435 | h1435
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1436 | h1436
                  · linarith only [h1406, h1408, h1436, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1406, h1435, h1436, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1439 | h1439
                  · linarith only [h1406, h1408, h1435, h1439, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1406, h1439, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1442 | h1442
              · linarith only [h1442, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1444 | h1444
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1445 | h1445
                  · linarith only [h1406, h1408, h1445, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1406, h1445, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1448 | h1448
                  · linarith only [h1406, h1408, h1448, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1406, h1448, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1431, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1452 | h1452
        · rcases p0_3 (m.d 3 6) (by simp) with h1453 | h1453
          · rcases p0_3 (m.d 4 6) (by simp) with h1454 | h1454
            · rcases p0_3 (m.d 5 6) (by simp) with h1455 | h1455
              · linarith only [h1455, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1457 | h1457
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1458 | h1458
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1459 | h1459
                    · linarith only [h1406, h1452, h1459, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1406, h1459, hc02, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h1408, h1454, h1458, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1463 | h1463
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1464 | h1464
                    · linarith only [h1406, h1452, h1464, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1406, h1464, hc02, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h1408, h1454, h1463, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1468 | h1468
              · linarith only [h1468, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1470 | h1470
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1471 | h1471
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1472 | h1472
                    · linarith only [h1406, h1452, h1472, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1406, h1452, h1472, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h1408, h1470, h1471, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1476 | h1476
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1477 | h1477
                    · linarith only [h1406, h1452, h1477, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1406, h1477, hc02, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h1408, h1476, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1453, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1482 | h1482
          · rcases p0_3 (m.d 4 6) (by simp) with h1483 | h1483
            · rcases p0_3 (m.d 5 6) (by simp) with h1484 | h1484
              · linarith only [h1484, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1486 | h1486
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1487 | h1487
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1488 | h1488
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1489 | h1489
                      · linarith only [h1406, h1489, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1406, h1489, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1452, h1483, h1488, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1408, h1483, h1486, h1487, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1494 | h1494
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1495 | h1495
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1496 | h1496
                      · linarith only [h1406, h1496, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1406, h1496, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1452, h1483, h1486, h1494, h1495, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                  · linarith only [h1408, h1483, h1494, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1501 | h1501
              · linarith only [h1501, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1503 | h1503
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1504 | h1504
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1505 | h1505
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1506 | h1506
                      · linarith only [h1406, h1506, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1406, h1506, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1452, h1505, hc02, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h1408, h1503, h1504, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1511 | h1511
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1512 | h1512
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1513 | h1513
                      · linarith only [h1406, h1513, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1406, h1513, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1452, h1503, h1511, h1512, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                  · linarith only [h1408, h1511, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1482, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1519 | h1519
    · linarith only [h1519, hlam, p0_0]
    · rcases p0_3 (m.d 1 6) (by simp) with h1521 | h1521
      · rcases p0_3 (m.d 2 6) (by simp) with h1522 | h1522
        · rcases p0_3 (m.d 3 6) (by simp) with h1523 | h1523
          · rcases p0_3 (m.d 4 6) (by simp) with h1524 | h1524
            · rcases p0_3 (m.d 5 6) (by simp) with h1525 | h1525
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1526 | h1526
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1527 | h1527
                  · linarith only [h1521, h1527, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1522, h1527, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1530 | h1530
                  · linarith only [h1521, h1530, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1530, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1533 | h1533
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1534 | h1534
                  · linarith only [h1521, h1534, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1534, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1537 | h1537
                  · linarith only [h1521, h1537, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1537, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1524, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1541 | h1541
            · rcases p0_3 (m.d 5 6) (by simp) with h1542 | h1542
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1543 | h1543
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1544 | h1544
                  · linarith only [h1521, h1544, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1544, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1547 | h1547
                  · linarith only [h1521, h1547, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1547, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1550 | h1550
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1551 | h1551
                  · linarith only [h1521, h1551, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1551, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1554 | h1554
                  · linarith only [h1521, h1550, h1554, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1554, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1541, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1558 | h1558
          · rcases p0_3 (m.d 4 6) (by simp) with h1559 | h1559
            · rcases p0_3 (m.d 5 6) (by simp) with h1560 | h1560
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1561 | h1561
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1562 | h1562
                  · linarith only [h1521, h1562, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1558, h1561, h1562, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1565 | h1565
                  · linarith only [h1521, h1565, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1565, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1568 | h1568
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1569 | h1569
                  · linarith only [h1521, h1569, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1569, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1572 | h1572
                  · linarith only [h1521, h1568, h1572, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1572, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1559, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1576 | h1576
            · rcases p0_3 (m.d 5 6) (by simp) with h1577 | h1577
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1578 | h1578
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1579 | h1579
                  · linarith only [h1521, h1579, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1578, h1579, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1582 | h1582
                  · linarith only [h1521, h1578, h1582, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1582, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1585 | h1585
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1586 | h1586
                  · linarith only [h1521, h1586, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1586, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1589 | h1589
                  · linarith only [h1521, h1585, h1589, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1589, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1576, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1593 | h1593
        · rcases p0_3 (m.d 3 6) (by simp) with h1594 | h1594
          · rcases p0_3 (m.d 4 6) (by simp) with h1595 | h1595
            · rcases p0_3 (m.d 5 6) (by simp) with h1596 | h1596
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1597 | h1597
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1598 | h1598
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1599 | h1599
                    · linarith only [h1593, h1597, h1598, h1599, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1594, h1599, hc02, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h1521, h1598, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1603 | h1603
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1604 | h1604
                    · linarith only [h1593, h1604, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1604, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1521, h1603, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1608 | h1608
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1609 | h1609
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1610 | h1610
                    · linarith only [h1593, h1610, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1610, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1521, h1609, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1614 | h1614
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1615 | h1615
                    · linarith only [h1593, h1615, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1615, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1521, h1614, hlam]
            · linarith only [h1595, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1620 | h1620
            · rcases p0_3 (m.d 5 6) (by simp) with h1621 | h1621
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1622 | h1622
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1623 | h1623
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1624 | h1624
                    · linarith only [h1593, h1624, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1624, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1521, h1623, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1628 | h1628
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1629 | h1629
                    · linarith only [h1593, h1629, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1629, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1521, h1628, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1633 | h1633
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1634 | h1634
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1635 | h1635
                    · linarith only [h1593, h1635, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1593, h1635, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h1521, h1634, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1639 | h1639
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1640 | h1640
                    · linarith only [h1593, h1640, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1640, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1521, h1639, hlam]
            · linarith only [h1620, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1645 | h1645
          · rcases p0_3 (m.d 4 6) (by simp) with h1646 | h1646
            · rcases p0_3 (m.d 5 6) (by simp) with h1647 | h1647
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1648 | h1648
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1649 | h1649
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1650 | h1650
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1651 | h1651
                      · linarith only [h1645, h1651, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1645, h1651, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1593, h1650, hlam]
                  · linarith only [h1521, h1649, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1656 | h1656
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1657 | h1657
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1658 | h1658
                      · linarith only [h1645, h1658, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1645, h1658, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1593, h1657, hlam]
                  · linarith only [h1521, h1656, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1663 | h1663
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1664 | h1664
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1665 | h1665
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1666 | h1666
                      · linarith only [h1645, h1666, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1645, h1666, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1593, h1665, hlam]
                  · linarith only [h1521, h1664, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1671 | h1671
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1672 | h1672
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1673 | h1673
                      · linarith only [h1645, h1673, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1645, h1673, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h1593, h1672, hlam]
                  · linarith only [h1521, h1671, hlam]
            · linarith only [h1646, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1679 | h1679
            · rcases p0_3 (m.d 5 6) (by simp) with h1680 | h1680
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1681 | h1681
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1682 | h1682
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1683 | h1683
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1684 | h1684
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h1685 | h1685
                        · linarith only [h1685, hlam, p0_0]
                        · linarith only [h1680, h1685, hc04, hc56, hlam, hphi, ht45, p0_1]
                      · linarith only [h1645, h1684, hlam]
                    · linarith only [h1593, h1683, hlam]
                  · linarith only [h1521, h1682, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1691 | h1691
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1692 | h1692
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1693 | h1693
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h1694 | h1694
                        · linarith only [h1694, hlam, p0_0]
                        · linarith only [h1680, h1694, hc04, hc56, hlam, hphi, ht45, p0_1]
                      · linarith only [h1645, h1693, hlam]
                    · linarith only [h1593, h1692, hlam]
                  · linarith only [h1521, h1691, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1700 | h1700
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1701 | h1701
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1702 | h1702
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1703 | h1703
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h1704 | h1704
                        · linarith only [h1704, hlam, p0_0]
                        · linarith only [h1704, hc04, hc46, hlam, hphi, p0_1]
                      · linarith only [h1645, h1703, hlam]
                    · linarith only [h1593, h1702, hlam]
                  · linarith only [h1521, h1701, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1710 | h1710
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1711 | h1711
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1712 | h1712
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h1713 | h1713
                        · linarith only [h1713, hlam, p0_0]
                        · linarith only [h1713, hc04, hc46, hlam, hphi, p0_1]
                      · linarith only [h1645, h1712, hlam]
                    · linarith only [h1593, h1711, hlam]
                  · linarith only [h1521, h1710, hlam]
            · linarith only [h1679, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1720 | h1720
    · linarith only [h1720, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h1722 | h1722
      · linarith only [h1722, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1724 | h1724
        · rcases p0_3 (m.d 3 6) (by simp) with h1725 | h1725
          · rcases p0_3 (m.d 4 6) (by simp) with h1726 | h1726
            · rcases p0_3 (m.d 5 6) (by simp) with h1727 | h1727
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1728 | h1728
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1729 | h1729
                  · linarith only [h1720, h1729, hlam]
                  · linarith only [h1724, h1728, h1729, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1732 | h1732
                  · linarith only [h1720, h1732, hlam]
                  · linarith only [h1727, h1732, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1735 | h1735
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1736 | h1736
                  · linarith only [h1720, h1736, hlam]
                  · linarith only [h1735, h1736, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1739 | h1739
                  · linarith only [h1720, h1739, hlam]
                  · linarith only [h1739, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1726, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1743 | h1743
            · rcases p0_3 (m.d 5 6) (by simp) with h1744 | h1744
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1745 | h1745
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1746 | h1746
                  · linarith only [h1720, h1746, hlam]
                  · linarith only [h1744, h1745, h1746, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1749 | h1749
                  · linarith only [h1720, h1749, hlam]
                  · linarith only [h1744, h1749, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1752 | h1752
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1753 | h1753
                  · linarith only [h1720, h1753, hlam]
                  · linarith only [h1752, h1753, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1756 | h1756
                  · linarith only [h1720, h1756, hlam]
                  · linarith only [h1756, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1743, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1760 | h1760
          · rcases p0_3 (m.d 4 6) (by simp) with h1761 | h1761
            · rcases p0_3 (m.d 5 6) (by simp) with h1762 | h1762
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1763 | h1763
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1764 | h1764
                  · linarith only [h1720, h1764, hlam]
                  · linarith only [h1762, h1763, h1764, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1767 | h1767
                  · linarith only [h1720, h1767, hlam]
                  · linarith only [h1762, h1767, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1770 | h1770
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1771 | h1771
                  · linarith only [h1720, h1771, hlam]
                  · linarith only [h1760, h1770, h1771, hc12, hc36, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1774 | h1774
                  · linarith only [h1720, h1774, hlam]
                  · linarith only [h1774, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1761, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1778 | h1778
            · rcases p0_3 (m.d 5 6) (by simp) with h1779 | h1779
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1780 | h1780
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1781 | h1781
                  · linarith only [h1720, h1781, hlam]
                  · linarith only [h1779, h1780, h1781, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1784 | h1784
                  · linarith only [h1720, h1784, hlam]
                  · linarith only [h1779, h1784, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1787 | h1787
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1788 | h1788
                  · linarith only [h1720, h1788, hlam]
                  · linarith only [h1787, h1788, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1791 | h1791
                  · linarith only [h1720, h1791, hlam]
                  · linarith only [h1791, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1778, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1795 | h1795
    · linarith only [h1795, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h1797 | h1797
      · rcases p0_3 (m.d 2 6) (by simp) with h1798 | h1798
        · linarith only [h1798, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1800 | h1800
          · rcases p0_3 (m.d 4 6) (by simp) with h1801 | h1801
            · rcases p0_3 (m.d 5 6) (by simp) with h1802 | h1802
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1803 | h1803
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1804 | h1804
                  · linarith only [h1797, h1804, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1795, h1800, h1804, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1807 | h1807
                  · linarith only [h1795, h1797, h1803, h1807, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1795, h1800, h1807, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1810 | h1810
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1811 | h1811
                  · linarith only [h1795, h1797, h1811, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1795, h1800, h1811, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1814 | h1814
                  · linarith only [h1795, h1797, h1810, h1814, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1795, h1814, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1801, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1818 | h1818
            · rcases p0_3 (m.d 5 6) (by simp) with h1819 | h1819
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1820 | h1820
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1821 | h1821
                  · linarith only [h1795, h1797, h1821, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1795, h1821, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1824 | h1824
                  · linarith only [h1795, h1797, h1820, h1824, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1795, h1824, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1827 | h1827
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1828 | h1828
                  · linarith only [h1795, h1797, h1828, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1795, h1828, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1831 | h1831
                  · linarith only [h1795, h1797, h1827, h1831, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1795, h1831, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1818, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1835 | h1835
        · linarith only [h1835, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1837 | h1837
          · rcases p0_3 (m.d 4 6) (by simp) with h1838 | h1838
            · rcases p0_3 (m.d 5 6) (by simp) with h1839 | h1839
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1840 | h1840
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1841 | h1841
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1842 | h1842
                    · linarith only [h1795, h1842, hlam]
                    · linarith only [h1839, h1842, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h1797, h1839, h1841, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1846 | h1846
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1847 | h1847
                    · linarith only [h1795, h1847, hlam]
                    · linarith only [h1839, h1840, h1846, h1847, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h1797, h1839, h1846, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1851 | h1851
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1852 | h1852
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1853 | h1853
                    · linarith only [h1795, h1853, hlam]
                    · linarith only [h1837, h1851, h1853, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · linarith only [h1797, h1851, h1852, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1857 | h1857
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1858 | h1858
                    · linarith only [h1795, h1858, hlam]
                    · linarith only [h1851, h1857, h1858, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                  · linarith only [h1797, h1857, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1838, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1863 | h1863
            · rcases p0_3 (m.d 5 6) (by simp) with h1864 | h1864
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1865 | h1865
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1866 | h1866
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1867 | h1867
                    · linarith only [h1795, h1867, hlam]
                    · linarith only [h1864, h1865, h1867, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h1797, h1864, h1865, h1866, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1871 | h1871
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1872 | h1872
                    · linarith only [h1795, h1872, hlam]
                    · linarith only [h1864, h1865, h1871, h1872, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h1797, h1864, h1871, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1876 | h1876
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1877 | h1877
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1878 | h1878
                    · linarith only [h1795, h1878, hlam]
                    · linarith only [h1876, h1878, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1797, h1876, h1877, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1882 | h1882
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1883 | h1883
                    · linarith only [h1795, h1883, hlam]
                    · linarith only [h1876, h1882, h1883, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                  · linarith only [h1797, h1882, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1863, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1888 | h1888
    · linarith only [h1888, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h1890 | h1890
      · rcases p0_3 (m.d 2 6) (by simp) with h1891 | h1891
        · rcases p0_3 (m.d 3 6) (by simp) with h1892 | h1892
          · linarith only [h1892, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1894 | h1894
            · rcases p0_3 (m.d 5 6) (by simp) with h1895 | h1895
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1896 | h1896
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1897 | h1897
                  · linarith only [h1890, h1897, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1888, h1891, h1897, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1900 | h1900
                  · linarith only [h1888, h1890, h1900, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1888, h1900, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1903 | h1903
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1904 | h1904
                  · linarith only [h1888, h1890, h1904, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1888, h1903, h1904, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1907 | h1907
                  · linarith only [h1888, h1890, h1907, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1888, h1907, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1894, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1911 | h1911
          · linarith only [h1911, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1913 | h1913
            · rcases p0_3 (m.d 5 6) (by simp) with h1914 | h1914
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1915 | h1915
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1916 | h1916
                  · linarith only [h1888, h1890, h1916, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1888, h1916, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1919 | h1919
                  · linarith only [h1888, h1890, h1919, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1888, h1919, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1922 | h1922
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1923 | h1923
                  · linarith only [h1888, h1890, h1923, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1888, h1923, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1926 | h1926
                  · linarith only [h1888, h1890, h1926, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1888, h1926, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1913, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1930 | h1930
        · rcases p0_3 (m.d 3 6) (by simp) with h1931 | h1931
          · linarith only [h1931, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1933 | h1933
            · rcases p0_3 (m.d 5 6) (by simp) with h1934 | h1934
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1935 | h1935
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1936 | h1936
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1937 | h1937
                    · linarith only [h1888, h1930, h1936, h1937, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1888, h1937, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1890, h1934, h1936, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1941 | h1941
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1942 | h1942
                    · linarith only [h1888, h1930, h1942, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1888, h1942, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1890, h1934, h1941, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1946 | h1946
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1947 | h1947
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1948 | h1948
                    · linarith only [h1888, h1930, h1948, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1888, h1948, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1890, h1947, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1952 | h1952
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1953 | h1953
                    · linarith only [h1888, h1930, h1953, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1888, h1953, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1890, h1952, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1933, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h1958 | h1958
          · linarith only [h1958, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h1960 | h1960
            · rcases p0_3 (m.d 5 6) (by simp) with h1961 | h1961
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1962 | h1962
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1963 | h1963
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1964 | h1964
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1965 | h1965
                      · linarith only [h1888, h1965, hlam]
                      · linarith only [h1961, h1965, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h1930, h1961, h1964, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h1890, h1961, h1962, h1963, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1970 | h1970
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1971 | h1971
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1972 | h1972
                      · linarith only [h1888, h1972, hlam]
                      · linarith only [h1961, h1972, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h1930, h1961, h1962, h1970, h1971, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h1890, h1961, h1970, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1977 | h1977
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1978 | h1978
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1979 | h1979
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1980 | h1980
                      · linarith only [h1888, h1980, hlam]
                      · linarith only [h1980, hc03, hc46, hlam, hphi, ht34, p0_1]
                    · linarith only [h1930, h1979, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1890, h1977, h1978, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h1985 | h1985
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h1986 | h1986
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1987 | h1987
                      · linarith only [h1888, h1987, hlam]
                      · linarith only [h1987, hc03, hc46, hlam, hphi, ht34, p0_1]
                    · linarith only [h1930, h1977, h1986, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · linarith only [h1890, h1985, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1960, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1994 | h1994
    · linarith only [h1994, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h1996 | h1996
      · rcases p0_3 (m.d 2 6) (by simp) with h1997 | h1997
        · rcases p0_3 (m.d 3 6) (by simp) with h1998 | h1998
          · rcases p0_3 (m.d 4 6) (by simp) with h1999 | h1999
            · rcases p0_3 (m.d 5 6) (by simp) with h2000 | h2000
              · linarith only [h2000, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2002 | h2002
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2003 | h2003
                  · linarith only [h1996, h2003, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1994, h1997, h2002, h2003, hc12, hc26, hlam, hphi, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2006 | h2006
                  · linarith only [h1994, h1996, h2006, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1994, h2006, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1999, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2010 | h2010
            · rcases p0_3 (m.d 5 6) (by simp) with h2011 | h2011
              · linarith only [h2011, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2013 | h2013
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2014 | h2014
                  · linarith only [h1994, h1996, h2014, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1994, h2014, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2017 | h2017
                  · linarith only [h1994, h1996, h2013, h2017, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1994, h2017, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h2010, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2021 | h2021
          · rcases p0_3 (m.d 4 6) (by simp) with h2022 | h2022
            · rcases p0_3 (m.d 5 6) (by simp) with h2023 | h2023
              · linarith only [h2023, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2025 | h2025
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2026 | h2026
                  · linarith only [h1994, h1996, h2026, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1994, h2021, h2026, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2029 | h2029
                  · linarith only [h1994, h1996, h2025, h2029, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h1994, h2029, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h2022, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2033 | h2033
            · rcases p0_3 (m.d 5 6) (by simp) with h2034 | h2034
              · linarith only [h2034, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2036 | h2036
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2037 | h2037
                  · linarith only [h1994, h1996, h2037, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1994, h2037, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2040 | h2040
                  · linarith only [h1994, h1996, h2040, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h1994, h2040, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h2033, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2044 | h2044
        · rcases p0_3 (m.d 3 6) (by simp) with h2045 | h2045
          · rcases p0_3 (m.d 4 6) (by simp) with h2046 | h2046
            · rcases p0_3 (m.d 5 6) (by simp) with h2047 | h2047
              · linarith only [h2047, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2049 | h2049
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2050 | h2050
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2051 | h2051
                    · linarith only [h1994, h2044, h2051, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1994, h2044, h2051, hc02, hc26, hlam, hphi, p0_1]
                  · linarith only [h1996, h2049, h2050, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2055 | h2055
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2056 | h2056
                    · linarith only [h1994, h2044, h2056, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1994, h2056, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1996, h2055, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h2046, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2061 | h2061
            · rcases p0_3 (m.d 5 6) (by simp) with h2062 | h2062
              · linarith only [h2062, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2064 | h2064
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2065 | h2065
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2066 | h2066
                    · linarith only [h1994, h2044, h2066, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1994, h2066, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1996, h2065, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2070 | h2070
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2071 | h2071
                    · linarith only [h1994, h2044, h2071, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1994, h2071, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1996, h2070, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h2061, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2076 | h2076
          · rcases p0_3 (m.d 4 6) (by simp) with h2077 | h2077
            · rcases p0_3 (m.d 5 6) (by simp) with h2078 | h2078
              · linarith only [h2078, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2080 | h2080
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2081 | h2081
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2082 | h2082
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2083 | h2083
                      · linarith only [h1994, h2076, h2083, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1994, h2076, h2083, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h2044, h2082, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1996, h2080, h2081, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2088 | h2088
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2089 | h2089
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2090 | h2090
                      · linarith only [h1994, h2076, h2090, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h1994, h2076, h2090, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h2044, h2080, h2089, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · linarith only [h1996, h2088, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h2077, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2096 | h2096
            · rcases p0_3 (m.d 5 6) (by simp) with h2097 | h2097
              · linarith only [h2097, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2099 | h2099
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2100 | h2100
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2101 | h2101
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2102 | h2102
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h2103 | h2103
                        · linarith only [h1994, h2103, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                        · linarith only [h1994, h2103, hc04, hc46, hlam, hphi, p0_1]
                      · linarith only [h2076, h2102, hc03, hc46, hlam, hphi, ht34, p0_1]
                    · linarith only [h2044, h2101, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1996, h2099, h2100, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2109 | h2109
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2110 | h2110
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2111 | h2111
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h2112 | h2112
                        · linarith only [h1994, h2112, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                        · linarith only [h1994, h2112, hc04, hc46, hlam, hphi, p0_1]
                      · linarith only [h2076, h2111, hc03, hc46, hlam, hphi, ht34, p0_1]
                    · linarith only [h2044, h2099, h2110, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · linarith only [h1996, h2109, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h2096, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2119 | h2119
    · linarith only [h2119, hlam, p0_0]
    · rcases p0_3 (m.d 1 6) (by simp) with h2121 | h2121
      · rcases p0_3 (m.d 2 6) (by simp) with h2122 | h2122
        · rcases p0_3 (m.d 3 6) (by simp) with h2123 | h2123
          · rcases p0_3 (m.d 4 6) (by simp) with h2124 | h2124
            · rcases p0_3 (m.d 5 6) (by simp) with h2125 | h2125
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2126 | h2126
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2127 | h2127
                  · linarith only [h2121, h2127, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2122, h2127, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2130 | h2130
                  · linarith only [h2121, h2130, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2130, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2125, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2134 | h2134
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2135 | h2135
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2136 | h2136
                  · linarith only [h2121, h2136, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2135, h2136, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2139 | h2139
                  · linarith only [h2121, h2139, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2139, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2134, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2143 | h2143
            · rcases p0_3 (m.d 5 6) (by simp) with h2144 | h2144
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2145 | h2145
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2146 | h2146
                  · linarith only [h2121, h2146, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2143, h2146, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2149 | h2149
                  · linarith only [h2121, h2149, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2149, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2144, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2153 | h2153
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2154 | h2154
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2155 | h2155
                  · linarith only [h2121, h2155, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2155, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2158 | h2158
                  · linarith only [h2121, h2154, h2158, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2158, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2153, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2162 | h2162
          · rcases p0_3 (m.d 4 6) (by simp) with h2163 | h2163
            · rcases p0_3 (m.d 5 6) (by simp) with h2164 | h2164
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2165 | h2165
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2166 | h2166
                  · linarith only [h2121, h2166, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2162, h2166, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2169 | h2169
                  · linarith only [h2121, h2169, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2169, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2164, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2173 | h2173
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2174 | h2174
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2175 | h2175
                  · linarith only [h2121, h2175, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2175, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2178 | h2178
                  · linarith only [h2121, h2174, h2178, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2178, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2173, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2182 | h2182
            · rcases p0_3 (m.d 5 6) (by simp) with h2183 | h2183
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2184 | h2184
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2185 | h2185
                  · linarith only [h2121, h2185, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2182, h2185, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2188 | h2188
                  · linarith only [h2121, h2184, h2188, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2188, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2183, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2192 | h2192
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2193 | h2193
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2194 | h2194
                  · linarith only [h2121, h2194, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2194, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2197 | h2197
                  · linarith only [h2121, h2193, h2197, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2197, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2192, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2201 | h2201
        · rcases p0_3 (m.d 3 6) (by simp) with h2202 | h2202
          · rcases p0_3 (m.d 4 6) (by simp) with h2203 | h2203
            · rcases p0_3 (m.d 5 6) (by simp) with h2204 | h2204
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2205 | h2205
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2206 | h2206
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2207 | h2207
                    · linarith only [h2201, h2205, h2206, h2207, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2207, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2121, h2206, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2211 | h2211
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2212 | h2212
                    · linarith only [h2201, h2211, h2212, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2212, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2121, h2211, hlam]
              · linarith only [h2204, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2217 | h2217
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2218 | h2218
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2219 | h2219
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2220 | h2220
                    · linarith only [h2201, h2219, h2220, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2220, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2121, h2219, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2224 | h2224
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2225 | h2225
                    · linarith only [h2201, h2224, h2225, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2225, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2121, h2224, hlam]
              · linarith only [h2217, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2230 | h2230
            · rcases p0_3 (m.d 5 6) (by simp) with h2231 | h2231
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2232 | h2232
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2233 | h2233
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2234 | h2234
                    · linarith only [h2201, h2233, h2234, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2234, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2121, h2233, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2238 | h2238
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2239 | h2239
                    · linarith only [h2201, h2238, h2239, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2232, h2239, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · linarith only [h2121, h2238, hlam]
              · linarith only [h2231, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2244 | h2244
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2245 | h2245
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2246 | h2246
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2247 | h2247
                    · linarith only [h2201, h2246, h2247, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2247, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2121, h2246, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2251 | h2251
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2252 | h2252
                    · linarith only [h2201, h2251, h2252, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2252, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2121, h2251, hlam]
              · linarith only [h2244, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2257 | h2257
          · rcases p0_3 (m.d 4 6) (by simp) with h2258 | h2258
            · rcases p0_3 (m.d 5 6) (by simp) with h2259 | h2259
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2260 | h2260
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2261 | h2261
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2262 | h2262
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2263 | h2263
                      · linarith only [h2257, h2261, h2263, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h2263, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h2201, h2262, hlam]
                  · linarith only [h2121, h2261, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2268 | h2268
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2269 | h2269
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2270 | h2270
                      · linarith only [h2257, h2268, h2270, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h2270, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h2201, h2269, hlam]
                  · linarith only [h2121, h2268, hlam]
              · linarith only [h2259, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2276 | h2276
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2277 | h2277
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2278 | h2278
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2279 | h2279
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2280 | h2280
                      · linarith only [h2257, h2278, h2280, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h2280, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h2201, h2279, hlam]
                  · linarith only [h2121, h2278, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2285 | h2285
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2286 | h2286
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2287 | h2287
                      · linarith only [h2257, h2285, h2287, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h2287, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h2201, h2286, hlam]
                  · linarith only [h2121, h2285, hlam]
              · linarith only [h2276, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2293 | h2293
            · rcases p0_3 (m.d 5 6) (by simp) with h2294 | h2294
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2295 | h2295
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2296 | h2296
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2297 | h2297
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2298 | h2298
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h2299 | h2299
                        · linarith only [h2293, h2296, h2299, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                        · linarith only [h2299, hc04, hc56, hlam, hphi, ht45, p0_1]
                      · linarith only [h2257, h2298, hlam]
                    · linarith only [h2201, h2297, hlam]
                  · linarith only [h2121, h2296, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2305 | h2305
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2306 | h2306
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2307 | h2307
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h2308 | h2308
                        · linarith only [h2293, h2305, h2308, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                        · linarith only [h2308, hc04, hc56, hlam, hphi, ht45, p0_1]
                      · linarith only [h2257, h2307, hlam]
                    · linarith only [h2201, h2306, hlam]
                  · linarith only [h2121, h2305, hlam]
              · linarith only [h2294, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2315 | h2315
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2316 | h2316
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2317 | h2317
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2318 | h2318
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2319 | h2319
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h2320 | h2320
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h2321 | h2321
                          · linarith only [h2321, hlam, p0_0]
                          · linarith only [h2321, hc05, hc56, hlam, hphi, p0_1]
                        · linarith only [h2293, h2320, hlam]
                      · linarith only [h2257, h2319, hlam]
                    · linarith only [h2201, h2318, hlam]
                  · linarith only [h2121, h2317, hlam]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2328 | h2328
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2329 | h2329
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2330 | h2330
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h2331 | h2331
                        · rcases m.htr 0 5 6 (by decide) (by decide) with h2332 | h2332
                          · linarith only [h2332, hlam, p0_0]
                          · linarith only [h2332, hc05, hc56, hlam, hphi, p0_1]
                        · linarith only [h2293, h2331, hlam]
                      · linarith only [h2257, h2330, hlam]
                    · linarith only [h2201, h2329, hlam]
                  · linarith only [h2121, h2328, hlam]
              · linarith only [h2315, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2340 | h2340
    · linarith only [h2340, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h2342 | h2342
      · linarith only [h2342, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2344 | h2344
        · rcases p0_3 (m.d 3 6) (by simp) with h2345 | h2345
          · rcases p0_3 (m.d 4 6) (by simp) with h2346 | h2346
            · rcases p0_3 (m.d 5 6) (by simp) with h2347 | h2347
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2348 | h2348
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2349 | h2349
                  · linarith only [h2340, h2349, hlam]
                  · linarith only [h2349, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2352 | h2352
                  · linarith only [h2340, h2352, hlam]
                  · linarith only [h2352, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2347, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2356 | h2356
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2357 | h2357
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2358 | h2358
                  · linarith only [h2340, h2358, hlam]
                  · linarith only [h2358, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2361 | h2361
                  · linarith only [h2340, h2361, hlam]
                  · linarith only [h2361, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2356, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2365 | h2365
            · rcases p0_3 (m.d 5 6) (by simp) with h2366 | h2366
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2367 | h2367
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2368 | h2368
                  · linarith only [h2340, h2368, hlam]
                  · linarith only [h2368, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2371 | h2371
                  · linarith only [h2340, h2371, hlam]
                  · linarith only [h2371, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2366, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2375 | h2375
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2376 | h2376
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2377 | h2377
                  · linarith only [h2340, h2377, hlam]
                  · linarith only [h2377, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2380 | h2380
                  · linarith only [h2340, h2380, hlam]
                  · linarith only [h2380, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2375, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2384 | h2384
          · rcases p0_3 (m.d 4 6) (by simp) with h2385 | h2385
            · rcases p0_3 (m.d 5 6) (by simp) with h2386 | h2386
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2387 | h2387
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2388 | h2388
                  · linarith only [h2340, h2388, hlam]
                  · linarith only [h2387, h2388, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2391 | h2391
                  · linarith only [h2340, h2391, hlam]
                  · linarith only [h2391, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2386, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2395 | h2395
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2396 | h2396
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2397 | h2397
                  · linarith only [h2340, h2397, hlam]
                  · linarith only [h2397, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2400 | h2400
                  · linarith only [h2340, h2400, hlam]
                  · linarith only [h2400, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2395, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2404 | h2404
            · rcases p0_3 (m.d 5 6) (by simp) with h2405 | h2405
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2406 | h2406
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2407 | h2407
                  · linarith only [h2340, h2407, hlam]
                  · linarith only [h2407, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2410 | h2410
                  · linarith only [h2340, h2410, hlam]
                  · linarith only [h2410, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2405, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2414 | h2414
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2415 | h2415
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2416 | h2416
                  · linarith only [h2340, h2416, hlam]
                  · linarith only [h2416, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2419 | h2419
                  · linarith only [h2340, h2419, hlam]
                  · linarith only [h2419, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2414, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2423 | h2423
    · linarith only [h2423, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h2425 | h2425
      · rcases p0_3 (m.d 2 6) (by simp) with h2426 | h2426
        · linarith only [h2426, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2428 | h2428
          · rcases p0_3 (m.d 4 6) (by simp) with h2429 | h2429
            · rcases p0_3 (m.d 5 6) (by simp) with h2430 | h2430
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2431 | h2431
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2432 | h2432
                  · linarith only [h2425, h2432, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2423, h2428, h2432, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2435 | h2435
                  · linarith only [h2423, h2425, h2435, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2423, h2435, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2430, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2439 | h2439
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2440 | h2440
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2441 | h2441
                  · linarith only [h2423, h2425, h2441, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2423, h2440, h2441, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2444 | h2444
                  · linarith only [h2423, h2425, h2440, h2444, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2423, h2444, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2439, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2448 | h2448
            · rcases p0_3 (m.d 5 6) (by simp) with h2449 | h2449
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2450 | h2450
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2451 | h2451
                  · linarith only [h2423, h2425, h2451, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2423, h2448, h2451, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2454 | h2454
                  · linarith only [h2423, h2425, h2450, h2454, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2423, h2454, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2449, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2458 | h2458
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2459 | h2459
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2460 | h2460
                  · linarith only [h2423, h2425, h2460, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2423, h2460, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2463 | h2463
                  · linarith only [h2423, h2425, h2459, h2463, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2423, h2463, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2458, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2467 | h2467
        · linarith only [h2467, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2469 | h2469
          · rcases p0_3 (m.d 4 6) (by simp) with h2470 | h2470
            · rcases p0_3 (m.d 5 6) (by simp) with h2471 | h2471
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2472 | h2472
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2473 | h2473
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2474 | h2474
                    · linarith only [h2423, h2474, hlam]
                    · linarith only [h2472, h2474, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2425, h2472, h2473, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2478 | h2478
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2479 | h2479
                    · linarith only [h2423, h2479, hlam]
                    · linarith only [h2472, h2479, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · linarith only [h2425, h2478, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2471, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2484 | h2484
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2485 | h2485
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2486 | h2486
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2487 | h2487
                    · linarith only [h2423, h2487, hlam]
                    · linarith only [h2487, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2425, h2485, h2486, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2491 | h2491
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2492 | h2492
                    · linarith only [h2423, h2492, hlam]
                    · linarith only [h2485, h2492, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · linarith only [h2425, h2491, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2484, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2497 | h2497
            · rcases p0_3 (m.d 5 6) (by simp) with h2498 | h2498
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2499 | h2499
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2500 | h2500
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2501 | h2501
                    · linarith only [h2423, h2501, hlam]
                    · linarith only [h2501, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2425, h2499, h2500, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2505 | h2505
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2506 | h2506
                    · linarith only [h2423, h2506, hlam]
                    · linarith only [h2499, h2505, h2506, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h2425, h2505, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2498, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2511 | h2511
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2512 | h2512
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2513 | h2513
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2514 | h2514
                    · linarith only [h2423, h2514, hlam]
                    · linarith only [h2512, h2514, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2425, h2512, h2513, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2518 | h2518
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2519 | h2519
                    · linarith only [h2423, h2519, hlam]
                    · linarith only [h2512, h2518, h2519, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h2425, h2518, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2511, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2524 | h2524
    · linarith only [h2524, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h2526 | h2526
      · rcases p0_3 (m.d 2 6) (by simp) with h2527 | h2527
        · rcases p0_3 (m.d 3 6) (by simp) with h2528 | h2528
          · linarith only [h2528, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2530 | h2530
            · rcases p0_3 (m.d 5 6) (by simp) with h2531 | h2531
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2532 | h2532
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2533 | h2533
                  · linarith only [h2526, h2533, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2524, h2527, h2533, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2536 | h2536
                  · linarith only [h2524, h2526, h2532, h2536, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2524, h2527, h2536, hc01, hc26, hlam, hphi, ht12, p0_1]
              · linarith only [h2531, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2540 | h2540
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2541 | h2541
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2542 | h2542
                  · linarith only [h2524, h2526, h2542, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2524, h2542, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2545 | h2545
                  · linarith only [h2524, h2526, h2541, h2545, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2524, h2545, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2540, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2549 | h2549
          · linarith only [h2549, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2551 | h2551
            · rcases p0_3 (m.d 5 6) (by simp) with h2552 | h2552
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2553 | h2553
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2554 | h2554
                  · linarith only [h2524, h2526, h2554, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2524, h2551, h2554, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2557 | h2557
                  · linarith only [h2524, h2526, h2553, h2557, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2524, h2557, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2552, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2561 | h2561
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2562 | h2562
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2563 | h2563
                  · linarith only [h2524, h2526, h2563, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2524, h2563, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2566 | h2566
                  · linarith only [h2524, h2526, h2562, h2566, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2524, h2566, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2561, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2570 | h2570
        · rcases p0_3 (m.d 3 6) (by simp) with h2571 | h2571
          · linarith only [h2571, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2573 | h2573
            · rcases p0_3 (m.d 5 6) (by simp) with h2574 | h2574
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2575 | h2575
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2576 | h2576
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2577 | h2577
                    · linarith only [h2524, h2570, h2575, h2576, h2577, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2524, h2573, h2577, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h2526, h2576, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2581 | h2581
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2582 | h2582
                    · linarith only [h2524, h2570, h2582, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2524, h2582, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2526, h2581, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2574, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2587 | h2587
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2588 | h2588
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2589 | h2589
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2590 | h2590
                    · linarith only [h2524, h2570, h2590, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2524, h2590, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2526, h2589, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2594 | h2594
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2595 | h2595
                    · linarith only [h2524, h2570, h2595, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2524, h2595, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2526, h2594, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2587, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2600 | h2600
          · linarith only [h2600, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2602 | h2602
            · rcases p0_3 (m.d 5 6) (by simp) with h2603 | h2603
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2604 | h2604
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2605 | h2605
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2606 | h2606
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2607 | h2607
                      · linarith only [h2524, h2607, hlam]
                      · linarith only [h2607, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h2570, h2606, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2526, h2604, h2605, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2612 | h2612
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2613 | h2613
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2614 | h2614
                      · linarith only [h2524, h2614, hlam]
                      · linarith only [h2614, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h2570, h2604, h2612, h2613, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h2526, h2612, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2603, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2620 | h2620
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2621 | h2621
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2622 | h2622
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2623 | h2623
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2624 | h2624
                      · linarith only [h2524, h2624, hlam]
                      · linarith only [h2624, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h2570, h2623, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2526, h2621, h2622, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2629 | h2629
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2630 | h2630
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2631 | h2631
                      · linarith only [h2524, h2631, hlam]
                      · linarith only [h2631, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h2570, h2621, h2629, h2630, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h2526, h2629, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2620, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2637 | h2637
    · linarith only [h2637, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h2639 | h2639
      · rcases p0_3 (m.d 2 6) (by simp) with h2640 | h2640
        · rcases p0_3 (m.d 3 6) (by simp) with h2641 | h2641
          · rcases p0_3 (m.d 4 6) (by simp) with h2642 | h2642
            · linarith only [h2642, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2644 | h2644
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2645 | h2645
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2646 | h2646
                  · linarith only [h2639, h2646, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2637, h2640, h2646, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2649 | h2649
                  · linarith only [h2637, h2639, h2645, h2649, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2637, h2640, h2649, hc01, hc26, hlam, hphi, ht12, p0_1]
              · linarith only [h2644, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2653 | h2653
            · linarith only [h2653, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2655 | h2655
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2656 | h2656
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2657 | h2657
                  · linarith only [h2637, h2639, h2657, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2637, h2640, h2657, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2660 | h2660
                  · linarith only [h2637, h2639, h2656, h2660, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2637, h2660, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2655, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2664 | h2664
          · rcases p0_3 (m.d 4 6) (by simp) with h2665 | h2665
            · linarith only [h2665, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2667 | h2667
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2668 | h2668
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2669 | h2669
                  · linarith only [h2637, h2639, h2669, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2637, h2664, h2669, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2672 | h2672
                  · linarith only [h2637, h2639, h2668, h2672, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2637, h2672, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2667, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2676 | h2676
            · linarith only [h2676, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2678 | h2678
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2679 | h2679
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2680 | h2680
                  · linarith only [h2637, h2639, h2680, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                  · linarith only [h2637, h2680, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2683 | h2683
                  · linarith only [h2637, h2639, h2679, h2683, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                  · linarith only [h2637, h2683, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2678, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2687 | h2687
        · rcases p0_3 (m.d 3 6) (by simp) with h2688 | h2688
          · rcases p0_3 (m.d 4 6) (by simp) with h2689 | h2689
            · linarith only [h2689, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2691 | h2691
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2692 | h2692
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2693 | h2693
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2694 | h2694
                    · linarith only [h2637, h2687, h2692, h2693, h2694, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2637, h2694, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2639, h2693, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2698 | h2698
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2699 | h2699
                    · linarith only [h2637, h2687, h2698, h2699, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2637, h2699, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2639, h2698, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2691, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2704 | h2704
            · linarith only [h2704, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2706 | h2706
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2707 | h2707
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2708 | h2708
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2709 | h2709
                    · linarith only [h2637, h2687, h2709, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2637, h2709, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2639, h2708, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2713 | h2713
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2714 | h2714
                    · linarith only [h2637, h2687, h2714, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2637, h2714, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2639, h2713, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2706, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h2719 | h2719
          · rcases p0_3 (m.d 4 6) (by simp) with h2720 | h2720
            · linarith only [h2720, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2722 | h2722
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2723 | h2723
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2724 | h2724
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2725 | h2725
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2726 | h2726
                      · linarith only [h2637, h2719, h2726, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h2637, h2719, h2726, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h2687, h2725, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2639, h2723, h2724, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2731 | h2731
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2732 | h2732
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2733 | h2733
                      · linarith only [h2637, h2719, h2733, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                      · linarith only [h2637, h2719, h2733, hc03, hc36, hlam, hphi, p0_1]
                    · linarith only [h2687, h2723, h2731, h2732, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                  · linarith only [h2639, h2731, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2722, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2739 | h2739
            · linarith only [h2739, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2741 | h2741
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2742 | h2742
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2743 | h2743
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2744 | h2744
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2745 | h2745
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h2746 | h2746
                        · linarith only [h2637, h2746, hlam]
                        · linarith only [h2746, hc04, hc56, hlam, hphi, ht45, p0_1]
                      · linarith only [h2719, h2745, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h2687, h2744, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · linarith only [h2639, h2742, h2743, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 6 (by decide) (by decide) with h2752 | h2752
                  · rcases m.htr 0 2 6 (by decide) (by decide) with h2753 | h2753
                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2754 | h2754
                      · rcases m.htr 0 4 6 (by decide) (by decide) with h2755 | h2755
                        · linarith only [h2637, h2755, hlam]
                        · linarith only [h2755, hc04, hc56, hlam, hphi, ht45, p0_1]
                      · linarith only [h2719, h2754, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                    · linarith only [h2687, h2742, h2753, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · linarith only [h2639, h2752, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
              · linarith only [h2741, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

set_option maxHeartbeats 4266000 in
theorem n8l_sBT8_M_LR_M_LR (m : N8Model)
    (hb0 : CMSig2_8_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_LR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h6elo := hb6.1
  have h6ehi := hb6.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi6 := h0ehi (m.d 0 1) (by simp)
  have u0ehi7 := h0ehi (m.d 0 2) (by simp)
  have u0ehi8 := h0ehi (m.d 0 3) (by simp)
  have u0ehi9 := h0ehi (m.d 0 4) (by simp)
  have u0ehi10 := h0ehi (m.d 0 5) (by simp)
  have u0ehi11 := h0ehi (m.d 0 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  have u6ehi7 := h6ehi (m.d 1 6) (by simp)
  have u6ehi8 := h6ehi (m.d 2 6) (by simp)
  have u6ehi9 := h6ehi (m.d 3 6) (by simp)
  have u6ehi10 := h6ehi (m.d 4 6) (by simp)
  have u6ehi11 := h6ehi (m.d 5 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 6 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h15, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h12, h15, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h12, h14, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                            · linarith only [h0, h12, h13, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                            · linarith only [h0, h12, h20, h4, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                              · linarith only [h0, h12, h22, h4, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h24 | h24
                                · linarith only [h0, h12, h24, h4, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h27 | h27
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h29 | h29
                                        · linarith only [h0, h12, h26, h29, h4, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · linarith only [h28, h29, hc45, hlam, hphi, ht56, u6elo4]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h32 | h32
                                        · linarith only [h10, h28, h32, h7, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h34 | h34
                                          · linarith only [h2, h34, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h38 | h38
                                                · linarith only [h0, h38, h4, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                                                · linarith only [h0, h12, h38, h4, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                                              · linarith only [h12, h27, h37, hlam]
                                            · linarith only [h12, h26, h36, hlam]
                                    · linarith only [h0, h26, h27, h4, h8, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
                                    · linarith only [h0, h26, h4, h44, h7, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h47 | h47
                                        · linarith only [h1, h47, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · linarith only [h46, h47, hc45, hlam, hphi, ht56, u6elo4]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h50 | h50
                                        · linarith only [h0, h10, h4, h46, h50, h7, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h52 | h52
                                          · linarith only [h2, h52, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                                            · linarith only [h0, h26, h4, h54, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                            · linarith only [h0, h12, h4, h54, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                        · linarith only [h11, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h58 | h58
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h62 | h62
                                · linarith only [h0, h62, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h61, h62, hc25, hlam, hphi, ht56, u6elo2]
                              · linarith only [h59, h6, h61, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h0, h5, h59, h60, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h67 | h67
                            · linarith only [h0, h4, h59, h67, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h69 | h69
                              · linarith only [h0, h4, h59, h69, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h71 | h71
                                · linarith only [h0, h4, h59, h71, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                                      · linarith only [h10, h75, hc14, hlam, hphi, ht01, u0ehi9]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h77 | h77
                                        · linarith only [h1, h77, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h79 | h79
                                          · linarith only [h0, h4, h59, h74, h79, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h83 | h83
                                                · linarith only [h0, h4, h83, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                                                · linarith only [h0, h4, h59, h83, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                                              · linarith only [h59, h74, h82, hlam]
                                            · linarith only [h58, h59, h73, h75, h79, h81, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo4]
                                    · linarith only [h0, h4, h73, h74, h8, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                                    · linarith only [h0, h4, h7, h73, h89, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                                      · linarith only [h10, h91, hc14, hlam, hphi, ht01, u0ehi9]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h93 | h93
                                        · linarith only [h1, h93, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h95 | h95
                                          · linarith only [h0, h4, h8, h89, h95, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                                            · linarith only [h0, h4, h73, h97, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                            · linarith only [h0, h4, h59, h7, h97, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                        · linarith only [h58, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h7, h9, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h102 | h102
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
                      · linarith only [h103, h7, h8, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h105 | h105
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h109 | h109
                                · linarith only [h0, h109, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h107, h109, hc24, hlam, hphi, ht45, ht56, u6elo2]
                              · linarith only [h106, h108, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h0, h106, h107, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                            · linarith only [h0, h106, h114, h4, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                              · linarith only [h0, h106, h116, h4, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h118 | h118
                                · linarith only [h0, h106, h118, h4, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h120 | h120
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                                    · linarith only [h121, h7, h8, hc13, hlam, hphi, ht01, u0ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                                      · linarith only [h103, h123, hc14, hlam, hphi, ht01, u0ehi9]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h125 | h125
                                        · linarith only [h1, h125, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h127 | h127
                                          · linarith only [h0, h116, h127, h6, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · linarith only [h0, h105, h120, h121, h127, h6, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                  · linarith only [h106, h120, h7, h8, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h105, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h102, h7, hc34, hlam, hphi, ht45, ht56, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h139 | h139
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h140 | h140
                                · linarith only [h0, h140, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h138, h140, hc24, hlam, hphi, ht45, ht56, u6elo2]
                              · linarith only [h0, h137, h139, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                            · linarith only [h0, h137, h138, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
                            · linarith only [h0, h137, h145, h4, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
                              · linarith only [h0, h137, h147, h4, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h149 | h149
                                · linarith only [h0, h137, h149, h4, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h151 | h151
                                  · linarith only [h133, h136, h151, h7, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h155 | h155
                                        · linarith only [h1, h155, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · linarith only [h154, h155, hc45, hlam, hphi, ht56, u6elo4]
                                      · linarith only [h135, h151, h153, h154, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo3]
                                    · linarith only [h133, h153, h7, hc13, hc34, hlam, hphi]
                        · linarith only [h136, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h133, h135, h7, hlam]
                    · linarith only [h133, h134, hc35, hlam, hphi, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h163 | h163
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h165 | h165
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h169 | h169
                                · linarith only [h0, h169, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h166, h169, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h166, h168, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                            · linarith only [h0, h166, h167, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h174 | h174
                            · linarith only [h0, h166, h174, h4, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h176 | h176
                              · linarith only [h0, h166, h176, h4, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h178 | h178
                                · linarith only [h0, h166, h178, h4, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
                                  · linarith only [h163, h180, h7, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h182 | h182
                                    · linarith only [h133, h163, h182, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h184 | h184
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h185 | h185
                                        · linarith only [h0, h174, h185, h5, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · linarith only [h184, h185, hc45, hlam, hphi, ht56, u6elo4]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h188 | h188
                                        · linarith only [h0, h164, h184, h188, h5, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h190 | h190
                                          · linarith only [h190, h2, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h192 | h192
                                            · linarith only [h0, h163, h192, h4, h7, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                                              · linarith only [h0, h133, h163, h192, h194, h5, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h196 | h196
                                                · linarith only [h0, h192, h196, h5, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                                                · linarith only [h163, h196, h7, hc23, hc34, hlam, hphi]
                        · linarith only [h165, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h200 | h200
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h201 | h201
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h202 | h202
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h203 | h203
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h204 | h204
                                · linarith only [h0, h204, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h201, h204, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h201, h203, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                            · linarith only [h0, h201, h202, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h209 | h209
                            · linarith only [h0, h201, h209, h4, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h211 | h211
                              · linarith only [h0, h201, h211, h4, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h213 | h213
                                · linarith only [h0, h201, h213, h4, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                                  · linarith only [h163, h215, h7, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h217 | h217
                                    · linarith only [h133, h163, h217, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h219 | h219
                                      · linarith only [h0, h164, h209, h219, h5, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h221 | h221
                                        · linarith only [h1, h221, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h223 | h223
                                          · linarith only [h0, h211, h223, h6, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
                                            · linarith only [h0, h163, h225, h4, h7, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                                              · linarith only [h0, h133, h163, h225, h227, h5, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h229 | h229
                                                · linarith only [h0, h225, h229, h5, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                                                · linarith only [h163, h229, h7, hc23, hc34, hlam, hphi]
                        · linarith only [h200, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h163, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h234 | h234
                · rcases m.htr 0 3 5 (by decide) (by decide) with h235 | h235
                  · linarith only [h235, h4, h6, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h237 | h237
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h238 | h238
                      · linarith only [h238, h5, h6, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h240 | h240
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h241 | h241
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h242 | h242
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h243 | h243
                              · linarith only [h237, h243, h4, h6, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h245 | h245
                                · linarith only [h2, h243, h245, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h241, h245, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                            · linarith only [h241, h242, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                          · linarith only [h241, h4, h6, hc12, hc25, hlam, hphi]
                        · linarith only [h240, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h234, h237, hc34, hlam, hphi, ht45, ht56, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h252 | h252
                  · linarith only [h252, h4, h6, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h254 | h254
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h255 | h255
                      · linarith only [h255, h5, h6, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h257 | h257
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h259 | h259
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h260 | h260
                              · linarith only [h0, h234, h254, h260, h5, h6, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h262 | h262
                                · linarith only [h2, h260, h262, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h258, h262, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                            · linarith only [h258, h259, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                          · linarith only [h258, h4, h6, hc12, hc25, hlam, hphi]
                        · linarith only [h257, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h254, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h269 | h269
              · rcases m.htr 0 3 4 (by decide) (by decide) with h270 | h270
                · linarith only [h270, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h272 | h272
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h273 | h273
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h274 | h274
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h275 | h275
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h277 | h277
                            · linarith only [h0, h277, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h279 | h279
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h280 | h280
                                · linarith only [h1, h277, h280, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h276, h280, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h269, h276, h279, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                          · linarith only [h276, h4, h5, hc12, hc24, hlam, hphi]
                        · linarith only [h275, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h269, h274, h5, hlam]
                    · linarith only [h272, h273, hc35, hlam, hphi, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h288 | h288
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h289 | h289
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h290 | h290
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h292 | h292
                            · linarith only [h292, h5, hc12, hlam, hphi, ht01, u0ehi7]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h295 | h295
                                · linarith only [h1, h292, h295, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h294, h295, hc25, hlam, hphi, ht56, u6elo2]
                              · linarith only [h269, h291, h294, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                          · linarith only [h291, h4, h5, hc12, hc24, hlam, hphi]
                        · linarith only [h272, h288, h290, hlam, hphi, u6ehi9, u6elo5]
                      · linarith only [h269, h289, h5, hlam]
                    · linarith only [h288, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h303 | h303
                · linarith only [h303, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h305 | h305
                  · linarith only [h269, h305, h4, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h307 | h307
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h308 | h308
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h309 | h309
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h310 | h310
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h311 | h311
                            · linarith only [h307, h311, h4, h5, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h313 | h313
                              · linarith only [h1, h269, h307, h311, h313, h4, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h315 | h315
                                · linarith only [h1, h311, h315, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h310, h315, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                          · linarith only [h310, h4, h5, hc12, hc24, hlam, hphi]
                        · linarith only [h269, h309, h4, hc23, hlam, hphi, ht34, ht45, ht56, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h320 | h320
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h321 | h321
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h322 | h322
                            · linarith only [h307, h322, h4, h5, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h324 | h324
                              · linarith only [h1, h269, h307, h322, h324, h4, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h326 | h326
                                · linarith only [h1, h322, h326, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h307, h308, h321, h326, h4, h5, hc23, hc45, hlam, hphi, ht34, u6ehi9, u6elo2]
                          · linarith only [h308, h321, h4, h5, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h307, h308, h320, h4, h5, hlam, hphi, u6ehi9, u6elo5]
                    · linarith only [h307, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h332 | h332
            · rcases m.htr 0 2 5 (by decide) (by decide) with h333 | h333
              · rcases m.htr 0 3 4 (by decide) (by decide) with h334 | h334
                · rcases m.htr 0 3 5 (by decide) (by decide) with h335 | h335
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h336 | h336
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h337 | h337
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h338 | h338
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
                          · linarith only [h332, h337, h338, h339, h4, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h341 | h341
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h343 | h343
                                · linarith only [h0, h343, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h341, h343, hc24, hlam, hphi, ht45, ht56, u6elo2]
                              · linarith only [h333, h341, h342, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h332, h341, h4, hc12, hc23, hlam, hphi]
                        · linarith only [h338, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h349 | h349
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h350 | h350
                          · linarith only [h350, h4, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h352 | h352
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h353 | h353
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h354 | h354
                                · linarith only [h0, h354, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h352, h354, hc24, hlam, hphi, ht45, ht56, u6elo2]
                              · linarith only [h333, h352, h353, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h332, h352, h4, hc12, hc23, hlam, hphi]
                        · linarith only [h337, h349, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi9, u6elo5]
                    · linarith only [h334, h336, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · linarith only [h333, h335, h4, hlam]
                · linarith only [h332, h334, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h363 | h363
                · rcases m.htr 0 3 5 (by decide) (by decide) with h364 | h364
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h365 | h365
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h366 | h366
                      · linarith only [h332, h333, h366, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h368 | h368
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h369 | h369
                          · linarith only [h369, h4, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h371 | h371
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h372 | h372
                              · linarith only [h0, h332, h333, h372, hlam, hphi, u0ehi9, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h374 | h374
                                · linarith only [h2, h372, h374, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h371, h374, hc24, hlam, hphi, ht45, ht56, u6elo2]
                            · linarith only [h332, h371, h4, hc12, hc23, hlam, hphi]
                        · linarith only [h332, h333, h368, hc24, hlam, hphi, ht45, ht56, u6elo5]
                    · linarith only [h332, h333, h364, h365, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi9, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h380 | h380
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h381 | h381
                      · linarith only [h332, h364, h381, h4, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h383 | h383
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h384 | h384
                          · linarith only [h332, h384, h4, hc12, hlam, hphi, ht01, u0ehi9]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h386 | h386
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h387 | h387
                              · linarith only [h0, h332, h333, h387, hlam, hphi, u0ehi9, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h389 | h389
                                · linarith only [h2, h387, h389, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h386, h389, hc24, hlam, hphi, ht45, ht56, u6elo2]
                            · linarith only [h332, h386, h4, hc12, hc23, hlam, hphi]
                        · linarith only [h364, h380, h383, hlam, hphi, u6ehi9, u6elo5]
                    · linarith only [h332, h380, h4, hc24, hlam, hphi, ht45, ht56, u6elo3]
                · linarith only [h332, h363, h4, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h396 | h396
              · rcases m.htr 0 3 4 (by decide) (by decide) with h397 | h397
                · rcases m.htr 0 3 5 (by decide) (by decide) with h398 | h398
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h399 | h399
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h400 | h400
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h401 | h401
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h402 | h402
                          · linarith only [h396, h4, h401, h402, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
                            · linarith only [h0, h332, h396, h401, h404, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h406 | h406
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h407 | h407
                                · linarith only [h1, h404, h407, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h406, h407, hc25, hlam, hphi, ht56, u6elo2]
                              · linarith only [h396, h4, h406, hc12, hc23, hlam, hphi]
                        · linarith only [h401, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h332, h396, h400, hlam]
                    · linarith only [h332, h396, h397, h399, hc25, hlam, hphi, ht56, u6elo3]
                  · linarith only [h332, h396, h397, h398, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h415 | h415
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h416 | h416
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h417 | h417
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h418 | h418
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
                          · linarith only [h0, h396, h4, h418, h419, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h421 | h421
                            · linarith only [h0, h332, h396, h418, h421, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h423 | h423
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h424 | h424
                                · linarith only [h1, h421, h424, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · linarith only [h423, h424, hc25, hlam, hphi, ht56, u6elo2]
                              · linarith only [h396, h4, h423, hc12, hc23, hlam, hphi]
                        · linarith only [h418, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h396, h397, h4, h417, hlam]
                    · linarith only [h396, h4, h416, hc25, hlam, hphi, ht56, u6elo3]
                  · linarith only [h396, h4, h415, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h432 | h432
                · rcases m.htr 0 3 5 (by decide) (by decide) with h433 | h433
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h434 | h434
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h435 | h435
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h436 | h436
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
                          · linarith only [h4, h437, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h439 | h439
                            · linarith only [h0, h332, h439, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h441 | h441
                              · linarith only [h1, h396, h439, h441, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h443 | h443
                                · linarith only [h1, h439, h443, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h445 | h445
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h446 | h446
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h447 | h447
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h448 | h448
                                        · linarith only [h1, h448, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · linarith only [h447, h448, hc45, hlam, hphi, ht56, u6elo4]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h451 | h451
                                        · linarith only [h432, h435, h447, h451, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h453 | h453
                                          · linarith only [h2, h453, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h455 | h455
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h456 | h456
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h457 | h457
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h458 | h458
                                                  · rcases m.htr 2 4 6 (by decide) (by decide) with h459 | h459
                                                    · rcases m.htr 2 5 6 (by decide) (by decide) with h460 | h460
                                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h461 | h461
                                                        · linarith only [h436, h445, h447, h453, h461, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo4]
                                                        · rcases m.htr 3 4 6 (by decide) (by decide) with h463 | h463
                                                          · linarith only [h432, h435, h436, h445, h447, h451, h453, h463, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi7]
                                                          · rcases m.htr 3 5 6 (by decide) (by decide) with h465 | h465
                                                            · linarith only [h433, h447, h453, h465, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                                            · rcases m.htr 4 5 6 (by decide) (by decide) with h467 | h467
                                                              · linarith only [h432, h435, h439, h447, h453, h467, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                                              · linarith only [h439, h447, h467, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo5]
                                                      · linarith only [h396, h432, h435, h436, h460, hlam, hphi, u0ehi7, u0elo2]
                                                    · linarith only [h396, h458, h459, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                                                  · linarith only [h332, h432, h435, h458, hlam, hphi, u0ehi7, u0elo2]
                                                · linarith only [h332, h432, h435, h436, h439, h447, h453, h455, h457, hc12, hc36, hlam, hphi, ht23, u0ehi7, u0elo2]
                                              · linarith only [h332, h432, h435, h436, h446, h453, h455, h456, hlam, hphi, u0ehi7, u0elo2]
                                            · linarith only [h4, h432, h435, h436, h439, h447, h453, h455, hc12, hc34, hlam, hphi, ht23, u0ehi7, u0elo2]
                                    · linarith only [h433, h445, h446, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h477 | h477
                                    · linarith only [h432, h445, h477, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo2]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h479 | h479
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h480 | h480
                                        · linarith only [h1, h480, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · linarith only [h479, h480, hc45, hlam, hphi, ht56, u6elo4]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h483 | h483
                                        · linarith only [h432, h435, h479, h483, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h485 | h485
                                          · linarith only [h2, h485, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h487 | h487
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h488 | h488
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h489 | h489
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h490 | h490
                                                  · rcases m.htr 2 4 6 (by decide) (by decide) with h491 | h491
                                                    · rcases m.htr 2 5 6 (by decide) (by decide) with h492 | h492
                                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h493 | h493
                                                        · linarith only [h432, h437, h445, h479, h493, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                                        · linarith only [h432, h435, h437, h445, h493, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                                      · linarith only [h396, h432, h435, h436, h492, hlam, hphi, u0ehi7, u0elo2]
                                                    · linarith only [h396, h490, h491, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                                                  · linarith only [h332, h432, h435, h490, hlam, hphi, u0ehi7, u0elo2]
                                                · linarith only [h4, h434, h489, hlam, hphi, u0ehi7, u0elo2]
                                              · linarith only [h332, h433, h487, h488, hlam, hphi, u0ehi7, u0elo2]
                                            · linarith only [h4, h432, h487, hlam, hphi, u0ehi7, u0elo2]
                        · linarith only [h436, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h503 | h503
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
                          · linarith only [h4, h504, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h506 | h506
                            · linarith only [h0, h332, h506, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h508 | h508
                              · linarith only [h1, h396, h506, h508, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h510 | h510
                                · linarith only [h1, h506, h510, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h512 | h512
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h513 | h513
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h514 | h514
                                      · linarith only [h1, h435, h514, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h516 | h516
                                        · linarith only [h2, h514, h516, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h518 | h518
                                          · linarith only [h2, h518, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h520 | h520
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h521 | h521
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h522 | h522
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h523 | h523
                                                  · linarith only [h332, h435, h520, h523, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                                  · linarith only [h2, h332, h503, h506, h514, h518, h523, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi7, u0elo0]
                                                · linarith only [h4, h434, h522, hlam, hphi, u0ehi7, u0elo2]
                                              · linarith only [h2, h332, h503, h513, h518, h520, h521, hlam, hphi, u0ehi7, u0elo0]
                                            · linarith only [h2, h503, h512, h514, h518, h520, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                                    · linarith only [h433, h512, h513, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h530 | h530
                                    · linarith only [h432, h512, h530, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo2]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h532 | h532
                                      · linarith only [h332, h435, h532, hc14, hlam, hphi, ht01, u0ehi7]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h534 | h534
                                        · linarith only [h1, h534, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h536 | h536
                                          · linarith only [h433, h530, h536, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h538 | h538
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h539 | h539
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h540 | h540
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h541 | h541
                                                  · linarith only [h2, h332, h435, h503, h504, h512, h532, h536, h538, h541, hc12, hc23, hlam, hphi, u0ehi7, u0elo0]
                                                  · linarith only [h2, h332, h503, h504, h512, h532, h536, h541, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi7, u0elo0]
                                                · linarith only [h4, h434, h540, hlam, hphi, u0ehi7, u0elo2]
                                              · linarith only [h332, h433, h538, h539, hlam, hphi, u0ehi7, u0elo2]
                                            · linarith only [h4, h432, h538, hlam, hphi, u0ehi7, u0elo2]
                        · linarith only [h503, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h432, h434, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h549 | h549
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h550 | h550
                      · linarith only [h432, h433, h550, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h552 | h552
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h553 | h553
                          · linarith only [h4, h553, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h555 | h555
                            · linarith only [h0, h332, h555, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h557 | h557
                              · linarith only [h1, h396, h555, h557, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h559 | h559
                                · linarith only [h1, h555, h559, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h561 | h561
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h562 | h562
                                    · linarith only [h433, h549, h562, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h564 | h564
                                      · linarith only [h2, h332, h550, h561, h562, h564, hlam, hphi, u0ehi7, u0elo0]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h566 | h566
                                        · linarith only [h2, h561, h562, h566, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h568 | h568
                                          · linarith only [h2, h568, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · linarith only [h2, h552, h561, h562, h568, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                  · linarith only [h432, h433, h553, h561, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h552, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h432, h549, hc34, hlam, hphi, ht45, ht56, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h574 | h574
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h575 | h575
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h576 | h576
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h577 | h577
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h578 | h578
                          · linarith only [h0, h4, h578, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h580 | h580
                            · linarith only [h0, h332, h580, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h582 | h582
                              · linarith only [h1, h396, h580, h582, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h584 | h584
                                · linarith only [h1, h580, h584, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h586 | h586
                                  · linarith only [h432, h574, h577, h586, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h588 | h588
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h589 | h589
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h590 | h590
                                        · linarith only [h1, h590, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · linarith only [h586, h588, h590, hc35, hlam, hphi, ht56, u6elo4]
                                      · linarith only [h576, h586, h588, h589, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo3]
                                    · linarith only [h432, h574, h588, hc13, hc34, hlam, hphi]
                        · linarith only [h396, h577, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi7, u6elo5]
                      · linarith only [h432, h574, h576, hlam]
                    · linarith only [h574, h575, hc35, hlam, hphi, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h598 | h598
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h599 | h599
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h600 | h600
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h601 | h601
                          · linarith only [h0, h4, h601, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h603 | h603
                            · linarith only [h0, h332, h603, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h605 | h605
                              · linarith only [h1, h396, h603, h605, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h607 | h607
                                · linarith only [h1, h603, h607, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h609 | h609
                                  · linarith only [h432, h598, h609, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h611 | h611
                                    · linarith only [h1, h574, h598, h609, h611, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h613 | h613
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h614 | h614
                                        · linarith only [h1, h614, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · linarith only [h613, h614, hc45, hlam, hphi, ht56, u6elo4]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h617 | h617
                                        · linarith only [h1, h599, h613, h617, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h619 | h619
                                          · linarith only [h2, h619, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h621 | h621
                                            · linarith only [h1, h432, h598, h599, h600, h601, h609, h613, h619, h621, hc12, hc23, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                                            · linarith only [h1, h4, h599, h600, h601, h609, h613, h619, h621, hc12, hc34, hlam, hphi, ht23, u0ehi7, u0elo0]
                        · linarith only [h600, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h625 | h625
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h626 | h626
                          · linarith only [h4, h626, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h628 | h628
                            · linarith only [h0, h332, h628, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h630 | h630
                              · linarith only [h1, h396, h628, h630, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h632 | h632
                                · linarith only [h1, h628, h632, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h634 | h634
                                  · linarith only [h432, h598, h634, hc13, hlam, hphi, ht01, u0ehi11, u6ehi9, u6elo0]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h636 | h636
                                    · linarith only [h1, h574, h598, h634, h636, hlam, hphi, u0ehi11, u0elo0, u6ehi9, u6elo0]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h638 | h638
                                      · linarith only [h1, h432, h598, h599, h638, hlam, hphi, u0ehi11, u0elo0, u6ehi9, u6elo0]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h640 | h640
                                        · linarith only [h2, h638, h640, hlam, hphi, u0ehi11, u0elo0, u6ehi10, u6elo0]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h642 | h642
                                          · linarith only [h2, h642, hlam, hphi, u0ehi11, u0elo0, u6ehi11, u6elo0]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h644 | h644
                                            · linarith only [h2, h432, h598, h625, h626, h634, h638, h642, h644, hc12, hc23, hlam, hphi, u0ehi11, u0elo0, u6ehi9, u6elo0]
                                            · linarith only [h2, h4, h625, h626, h634, h638, h642, h644, hc12, hc34, hlam, hphi, ht23, u0ehi7, u0elo0]
                        · linarith only [h625, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h598, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi6, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h650 | h650
        · rcases m.htr 0 2 3 (by decide) (by decide) with h651 | h651
          · rcases m.htr 0 2 4 (by decide) (by decide) with h652 | h652
            · rcases m.htr 0 2 5 (by decide) (by decide) with h653 | h653
              · linarith only [h0, h2, h653, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h655 | h655
                · rcases m.htr 0 3 5 (by decide) (by decide) with h656 | h656
                  · linarith only [h0, h2, h651, h656, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h658 | h658
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h659 | h659
                      · linarith only [h0, h2, h651, h655, h659, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h661 | h661
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h662 | h662
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h663 | h663
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h664 | h664
                              · linarith only [h0, h653, h664, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h666 | h666
                                · linarith only [h0, h2, h664, h666, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · linarith only [h662, h666, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                            · linarith only [h652, h662, h663, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                          · linarith only [h651, h653, h662, hc12, hc25, hlam, hphi]
                        · linarith only [h661, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h655, h658, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi9, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h673 | h673
                  · linarith only [h1, h2, h655, h673, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h675 | h675
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h676 | h676
                      · linarith only [h0, h2, h652, h676, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h678 | h678
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h679 | h679
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h680 | h680
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h681 | h681
                              · linarith only [h0, h652, h653, h655, h675, h681, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h683 | h683
                                · linarith only [h0, h2, h681, h683, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · linarith only [h679, h683, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                            · linarith only [h652, h679, h680, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                          · linarith only [h651, h653, h679, hc12, hc25, hlam, hphi]
                        · linarith only [h678, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h675, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h690 | h690
              · linarith only [h1, h2, h652, h690, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h692 | h692
                · linarith only [h651, h652, h692, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h694 | h694
                  · linarith only [h1, h2, h651, h652, h694, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h696 | h696
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h697 | h697
                      · linarith only [h1, h2, h697, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h699 | h699
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h700 | h700
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h701 | h701
                            · linarith only [h651, h652, h696, h701, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h703 | h703
                              · linarith only [h1, h2, h651, h690, h696, h701, h703, hc15, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h705 | h705
                                · linarith only [h1, h2, h701, h703, h705, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · linarith only [h651, h652, h696, h697, h700, h705, hc23, hc45, hlam, hphi, ht34, u6ehi9, u6elo2]
                          · linarith only [h651, h652, h697, h700, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h1, h2, h651, h652, h696, h697, h699, hc14, hc45, hlam, hphi, u6ehi9, u6elo5]
                    · linarith only [h696, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h711 | h711
            · rcases m.htr 0 2 5 (by decide) (by decide) with h712 | h712
              · linarith only [h0, h2, h712, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h714 | h714
                · rcases m.htr 0 3 5 (by decide) (by decide) with h715 | h715
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h716 | h716
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h717 | h717
                      · linarith only [h1, h2, h717, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h719 | h719
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h720 | h720
                          · linarith only [h651, h720, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h722 | h722
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h723 | h723
                              · linarith only [h0, h711, h712, h723, hlam, hphi, u0ehi9, u0elo0]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h725 | h725
                                · linarith only [h0, h2, h723, h725, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · linarith only [h722, h725, hc24, hlam, hphi, ht45, ht56, u6elo2]
                            · linarith only [h651, h711, h722, hc12, hc23, hlam, hphi]
                        · linarith only [h719, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h714, h716, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h731 | h731
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h732 | h732
                      · linarith only [h0, h2, h711, h732, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h734 | h734
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h735 | h735
                          · linarith only [h0, h651, h711, h735, hlam, hphi, u0ehi9, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h737 | h737
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h738 | h738
                              · linarith only [h0, h2, h711, h712, h738, hlam, hphi, u0ehi9, u0elo4]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h740 | h740
                                · linarith only [h0, h2, h738, h740, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · linarith only [h737, h740, hc24, hlam, hphi, ht45, ht56, u6elo2]
                            · linarith only [h651, h711, h737, hc12, hc23, hlam, hphi]
                        · linarith only [h734, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h651, h711, h731, hc24, hlam, hphi, ht45, ht56, u6elo3]
                · linarith only [h651, h711, h714, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h747 | h747
              · linarith only [h0, h2, h747, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h749 | h749
                · rcases m.htr 0 3 5 (by decide) (by decide) with h750 | h750
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h751 | h751
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h752 | h752
                      · linarith only [h1, h2, h752, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h754 | h754
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h755 | h755
                          · linarith only [h651, h755, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h757 | h757
                            · linarith only [h0, h711, h757, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h759 | h759
                              · linarith only [h1, h2, h747, h750, h757, h759, hlam, hphi, u0ehi7, u0elo2]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h761 | h761
                                · linarith only [h1, h2, h757, h759, h761, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h763 | h763
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h764 | h764
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h765 | h765
                                      · linarith only [h1, h2, h752, h755, h764, h765, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h767 | h767
                                        · linarith only [h1, h2, h765, h767, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h769 | h769
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h770 | h770
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h771 | h771
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h772 | h772
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h773 | h773
                                                  · linarith only [h2, h765, h773, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                                                  · linarith only [h711, h773, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                                                · linarith only [h651, h751, h772, hlam, hphi, u0ehi7, u0elo2]
                                              · linarith only [h1, h2, h711, h750, h755, h764, h771, hlam, hphi, u0ehi7, u0elo2]
                                            · linarith only [h1, h2, h711, h755, h764, h770, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                          · linarith only [h1, h2, h711, h769, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7]
                                    · linarith only [h750, h763, h764, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h781 | h781
                                    · linarith only [h749, h763, h781, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo2]
                                    · linarith only [h1, h2, h750, h781, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                        · linarith only [h754, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h749, h751, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h786 | h786
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h787 | h787
                      · linarith only [h1, h2, h787, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h789 | h789
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h790 | h790
                          · linarith only [h651, h790, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h792 | h792
                            · linarith only [h0, h711, h792, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h794 | h794
                              · linarith only [h1, h2, h747, h792, h794, hlam, hphi, u0ehi7, u0elo4]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h796 | h796
                                · linarith only [h1, h2, h792, h794, h796, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h798 | h798
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h799 | h799
                                    · linarith only [h711, h749, h750, h799, hc13, hlam, hphi, ht01, u0ehi7]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h801 | h801
                                      · linarith only [h1, h2, h711, h787, h799, h801, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h803 | h803
                                        · linarith only [h1, h2, h801, h803, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h805 | h805
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h806 | h806
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h807 | h807
                                              · linarith only [h711, h749, h750, h807, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                              · linarith only [h651, h807, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                            · linarith only [h651, h806, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                          · linarith only [h2, h805, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6]
                                  · linarith only [h749, h750, h798, hc13, hc35, hlam, hphi]
                        · linarith only [h789, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h749, h786, hc34, hlam, hphi, ht45, ht56, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h815 | h815
                  · linarith only [h1, h2, h749, h815, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h817 | h817
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h818 | h818
                      · linarith only [h1, h2, h818, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h820 | h820
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h821 | h821
                          · linarith only [h651, h821, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h823 | h823
                            · linarith only [h0, h711, h823, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h825 | h825
                              · linarith only [h1, h2, h747, h823, h825, hlam, hphi, u0ehi7, u0elo4]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h827 | h827
                                · linarith only [h1, h2, h823, h825, h827, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h829 | h829
                                  · linarith only [h651, h749, h829, hc13, hlam, hphi, ht01, u0ehi7]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h831 | h831
                                    · linarith only [h1, h2, h651, h815, h825, h829, h831, hc25, hlam, hphi, ht01, ht12, u0ehi7]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h833 | h833
                                      · linarith only [h1, h2, h651, h749, h818, h831, h833, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h835 | h835
                                        · linarith only [h1, h2, h833, h835, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h837 | h837
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h838 | h838
                                            · linarith only [h651, h749, h838, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                            · linarith only [h651, h838, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                          · linarith only [h2, h837, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6]
                        · linarith only [h820, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h651, h817, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi7, u6elo3]
        · linarith only [h650, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi6, u6elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h845 | h845
      · rcases m.htr 0 1 6 (by decide) (by decide) with h846 | h846
        · rcases m.htr 0 2 3 (by decide) (by decide) with h847 | h847
          · rcases m.htr 0 2 4 (by decide) (by decide) with h848 | h848
            · linarith only [h0, h1, h848, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h850 | h850
              · rcases m.htr 0 3 4 (by decide) (by decide) with h851 | h851
                · linarith only [h0, h1, h847, h851, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h853 | h853
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h854 | h854
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h855 | h855
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h856 | h856
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h857 | h857
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h858 | h858
                            · linarith only [h0, h847, h848, h853, h856, h858, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h860 | h860
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h861 | h861
                                · linarith only [h0, h1, h858, h861, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · linarith only [h857, h861, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h850, h857, h860, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                          · linarith only [h847, h848, h857, hc12, hc24, hlam, hphi]
                        · linarith only [h856, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h1, h845, h855, hlam]
                    · linarith only [h853, h854, hc35, hlam, hphi, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h869 | h869
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h870 | h870
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h871 | h871
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h872 | h872
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h873 | h873
                            · linarith only [h0, h848, h873, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h875 | h875
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h876 | h876
                                · linarith only [h0, h1, h873, h876, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · linarith only [h872, h876, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                              · linarith only [h850, h872, h875, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                          · linarith only [h847, h848, h872, hc12, hc24, hlam, hphi]
                        · linarith only [h853, h869, h871, hlam, hphi, u6ehi9, u6elo5]
                      · linarith only [h0, h1, h850, h870, hlam]
                    · linarith only [h869, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h884 | h884
                · linarith only [h1, h845, h847, h850, h884, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h886 | h886
                  · linarith only [h847, h850, h886, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h888 | h888
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h889 | h889
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h890 | h890
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h891 | h891
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h892 | h892
                            · linarith only [h0, h847, h848, h888, h892, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h894 | h894
                              · linarith only [h0, h1, h847, h850, h888, h892, h894, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h896 | h896
                                · linarith only [h1, h845, h892, h894, h896, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · linarith only [h891, h896, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                          · linarith only [h847, h850, h891, hc12, hc25, hlam, hphi]
                        · linarith only [h847, h850, h890, hc23, hlam, hphi, ht34, ht45, ht56, u6elo5]
                      · linarith only [h1, h845, h889, hlam]
                    · linarith only [h888, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h903 | h903
            · linarith only [h0, h1, h903, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h905 | h905
              · rcases m.htr 0 3 4 (by decide) (by decide) with h906 | h906
                · rcases m.htr 0 3 5 (by decide) (by decide) with h907 | h907
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h908 | h908
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h909 | h909
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h910 | h910
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h911 | h911
                          · linarith only [h847, h905, h910, h911, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h913 | h913
                            · linarith only [h0, h1, h903, h905, h906, h910, h913, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi11]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h915 | h915
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h916 | h916
                                · linarith only [h0, h1, h913, h916, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · linarith only [h915, h916, hc25, hlam, hphi, ht56, u6elo2]
                              · linarith only [h847, h905, h915, hc12, hc23, hlam, hphi]
                        · linarith only [h910, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h1, h845, h909, hlam]
                    · linarith only [h0, h1, h905, h906, h908, hc25, hlam, hphi, ht56, u6elo3]
                  · linarith only [h0, h1, h905, h906, h907, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h924 | h924
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h925 | h925
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h926 | h926
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h927 | h927
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h928 | h928
                          · linarith only [h0, h847, h905, h927, h928, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h930 | h930
                            · linarith only [h0, h1, h903, h905, h927, h930, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi11]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h932 | h932
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h933 | h933
                                · linarith only [h0, h1, h930, h933, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · linarith only [h932, h933, hc25, hlam, hphi, ht56, u6elo2]
                              · linarith only [h847, h905, h932, hc12, hc23, hlam, hphi]
                        · linarith only [h927, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h1, h845, h926, hlam]
                    · linarith only [h924, h925, hc35, hlam, hphi, ht56, u6elo3]
                  · linarith only [h847, h905, h924, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h941 | h941
                · rcases m.htr 0 3 5 (by decide) (by decide) with h942 | h942
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h943 | h943
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h944 | h944
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h945 | h945
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h946 | h946
                          · linarith only [h0, h847, h946, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h948 | h948
                            · linarith only [h0, h1, h903, h941, h948, hlam, hphi, u0ehi7, u0elo2]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h950 | h950
                              · linarith only [h0, h1, h905, h948, h950, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h952 | h952
                                · linarith only [h1, h845, h948, h950, h952, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h954 | h954
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h955 | h955
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h956 | h956
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h957 | h957
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h958 | h958
                                          · linarith only [h1, h845, h946, h954, h958, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                                          · linarith only [h1, h845, h945, h946, h950, h954, h958, hc12, hc23, hlam, hphi]
                                        · linarith only [h1, h845, h945, h957, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi11]
                                      · linarith only [h1, h845, h945, h956, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi11]
                                    · linarith only [h942, h954, h955, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h1, h845, h941, h945, h954, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi11]
                        · linarith only [h945, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h1, h845, h944, hlam]
                    · linarith only [h941, h943, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · linarith only [h1, h845, h941, h942, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h969 | h969
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h970 | h970
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h971 | h971
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h972 | h972
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h973 | h973
                          · linarith only [h0, h847, h973, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h975 | h975
                            · linarith only [h0, h1, h903, h975, hc14, hlam, hphi, ht01, u0ehi7]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h977 | h977
                              · linarith only [h0, h1, h905, h975, h977, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h979 | h979
                                · linarith only [h1, h845, h975, h977, h979, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h981 | h981
                                  · linarith only [h941, h970, h981, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h983 | h983
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h984 | h984
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h985 | h985
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h986 | h986
                                          · linarith only [h1, h845, h981, h986, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi11]
                                          · linarith only [h1, h845, h972, h977, h981, h986, hc12, hc34, hlam, hphi, ht23]
                                        · linarith only [h1, h846, h985, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi7]
                                      · linarith only [h1, h845, h972, h984, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi11]
                                    · linarith only [h941, h969, h983, hc13, hc34, hlam, hphi]
                        · linarith only [h972, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h1, h845, h971, hlam]
                    · linarith only [h969, h970, hc35, hlam, hphi, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h995 | h995
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h996 | h996
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h997 | h997
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h998 | h998
                          · linarith only [h0, h847, h998, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1000 | h1000
                            · linarith only [h0, h1, h1000, h903, hlam, hphi, u0ehi7, u0elo3]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1002 | h1002
                              · linarith only [h0, h1, h1000, h1002, h905, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1004 | h1004
                                · linarith only [h1, h1000, h1002, h1004, h845, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1006 | h1006
                                  · linarith only [h1006, h847, h941, hc13, hlam, hphi, ht01, u0ehi7]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1008 | h1008
                                    · linarith only [h1006, h1008, h847, h969, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1010 | h1010
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1011 | h1011
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1012 | h1012
                                          · linarith only [h1, h1006, h1012, h845, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi11]
                                          · linarith only [h1, h1006, h1008, h1012, h845, h997, hc13, hc34, hlam, hphi]
                                        · linarith only [h1, h1011, h845, h969, h995, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi9]
                                      · linarith only [h1, h1010, h845, h969, h995, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi9]
                        · linarith only [h969, h995, h997, hlam, hphi, u6ehi9, u6elo5]
                      · linarith only [h1, h845, h996, hlam]
                    · linarith only [h995, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
        · linarith only [h846, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi6, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h1021 | h1021
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1022 | h1022
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1023 | h1023
            · linarith only [h0, h1, h1023, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1025 | h1025
              · linarith only [h0, h1025, h845, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1027 | h1027
                · linarith only [h0, h1, h1022, h1027, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1029 | h1029
                  · linarith only [h0, h1022, h1029, h845, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1031 | h1031
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1032 | h1032
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1033 | h1033
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1034 | h1034
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1035 | h1035
                            · linarith only [h0, h1023, h1035, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1037 | h1037
                              · linarith only [h0, h1, h1022, h1025, h1031, h1035, h1037, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1039 | h1039
                                · linarith only [h0, h1, h1035, h1039, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · linarith only [h1034, h1039, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                          · linarith only [h1022, h1023, h1034, hc12, hc24, hlam, hphi]
                        · linarith only [h1033, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1044 | h1044
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1045 | h1045
                          · linarith only [h0, h1, h1032, h1045, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h1, h1022, h1032, h1045, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h1, h1022, h1031, h1032, h1044, hlam, hphi, u6ehi9, u6elo5]
                    · linarith only [h1031, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1050 | h1050
            · linarith only [h0, h1, h1050, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1052 | h1052
              · linarith only [h0, h1052, h845, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1054 | h1054
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1055 | h1055
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1056 | h1056
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1057 | h1057
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1058 | h1058
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1059 | h1059
                          · linarith only [h1022, h1059, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1061 | h1061
                            · linarith only [h0, h1050, h1061, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1063 | h1063
                              · linarith only [h0, h1052, h1054, h1057, h1063, h845, hlam, hphi, u0ehi7, u0elo2]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1065 | h1065
                                · linarith only [h0, h1054, h1057, h1065, h845, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1067 | h1067
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1068 | h1068
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1069 | h1069
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1070 | h1070
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1071 | h1071
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1072 | h1072
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1073 | h1073
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1074 | h1074
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1075 | h1075
                                                  · rcases m.htr 2 4 6 (by decide) (by decide) with h1076 | h1076
                                                    · rcases m.htr 2 5 6 (by decide) (by decide) with h1077 | h1077
                                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1078 | h1078
                                                        · rcases m.htr 3 4 6 (by decide) (by decide) with h1079 | h1079
                                                          · linarith only [h1054, h1079, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi10]
                                                          · linarith only [h1070, h1078, h1079, hc45, hlam, hphi, ht56, u6elo1]
                                                        · rcases m.htr 3 4 6 (by decide) (by decide) with h1082 | h1082
                                                          · linarith only [h1054, h1057, h1078, h1082, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi10]
                                                          · rcases m.htr 3 5 6 (by decide) (by decide) with h1084 | h1084
                                                            · linarith only [h1055, h1084, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi11]
                                                            · rcases m.htr 4 5 6 (by decide) (by decide) with h1086 | h1086
                                                              · linarith only [h1054, h1057, h1078, h1084, h1086, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                                              · linarith only [h1078, h1086, hc34, hlam, hphi, ht45, ht56, u6elo5]
                                                      · linarith only [h1021, h1063, h1071, h1077, h845, hlam]
                                                    · linarith only [h1021, h1061, h1069, h1070, h1076, h845, hlam]
                                                  · linarith only [h1021, h1061, h1069, h1075, h845, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi7]
                                                · linarith only [h1022, h1056, h1074, hlam, hphi, u0ehi7, u0elo2]
                                              · linarith only [h1021, h1059, h1067, h1069, h1070, h1073, h845, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi10]
                                            · linarith only [h1021, h1059, h1067, h1069, h1070, h1072, h845, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi10]
                                          · linarith only [h1021, h1070, h1071, h845, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u6ehi10]
                                        · linarith only [h1021, h1069, h1070, h845, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi7]
                                      · linarith only [h1, h1021, h1054, h1057, h1069, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi7]
                                    · linarith only [h1, h1021, h1055, h1067, h1068, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi7]
                                  · linarith only [h1, h1021, h1054, h1067, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi7]
                        · linarith only [h1058, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1101 | h1101
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1102 | h1102
                          · linarith only [h1022, h1102, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1104 | h1104
                            · linarith only [h0, h1, h1057, h1104, hc24, hc45, hlam, hphi]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1106 | h1106
                              · linarith only [h0, h1, h1052, h1057, h1106, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1108 | h1108
                                · linarith only [h0, h1, h1057, h1108, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1110 | h1110
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1111 | h1111
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1112 | h1112
                                      · linarith only [h1, h1057, h1102, h1110, h1112, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                                      · linarith only [h0, h1, h1112, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                                    · linarith only [h1055, h1110, h1111, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h0, h1, h1054, h1110, hlam, hphi, u0ehi7, u0elo2]
                        · linarith only [h0, h1, h1057, h1101, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi7, u6elo5]
                    · linarith only [h1054, h1056, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1119 | h1119
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1120 | h1120
                      · linarith only [h1054, h1055, h1120, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1122 | h1122
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1123 | h1123
                          · linarith only [h0, h1, h1054, h1055, h1123, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1125 | h1125
                            · linarith only [h0, h1, h1120, h1125, hc24, hc45, hlam, hphi]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1127 | h1127
                              · linarith only [h0, h1, h1052, h1054, h1055, h1127, hc02, hc35, hlam, hphi, ht23]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1129 | h1129
                                · linarith only [h0, h1, h1054, h1055, h1129, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1131 | h1131
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1132 | h1132
                                    · linarith only [h1, h1021, h1054, h1055, h1132, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                                    · linarith only [h1, h1021, h1131, h1132, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi7]
                                  · linarith only [h1054, h1055, h1131, hc13, hc35, hlam, hphi]
                        · linarith only [h1055, h1119, h1122, hlam, hphi, u6ehi9, u6elo5]
                    · linarith only [h1, h1021, h1054, h1119, hlam, hphi, u6ehi7, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1138 | h1138
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1139 | h1139
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1140 | h1140
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1141 | h1141
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1142 | h1142
                          · linarith only [h0, h1054, h1138, h1142, h845, hc23, hc34, hlam, hphi]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1144 | h1144
                            · linarith only [h0, h1050, h1054, h1138, h1144, h845, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1146 | h1146
                              · linarith only [h0, h1052, h1054, h1138, h1146, h845, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1148 | h1148
                                · linarith only [h0, h1054, h1138, h1148, h845, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1150 | h1150
                                  · linarith only [h1054, h1139, h1150, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1152 | h1152
                                    · linarith only [h0, h1150, h1152, h845, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                    · linarith only [h1054, h1138, h1152, hc13, hc34, hlam, hphi]
                        · linarith only [h0, h1141, h845, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi7, u6elo5]
                      · linarith only [h1054, h1138, h1140, hlam]
                    · linarith only [h1021, h1138, h1139, h845, hlam, hphi, u6ehi7, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1158 | h1158
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1159 | h1159
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1160 | h1160
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1161 | h1161
                          · linarith only [h0, h1022, h1161, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1163 | h1163
                            · linarith only [h0, h1050, h1159, h1163, h845, hlam, hphi, u0ehi7, u0elo3]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1165 | h1165
                              · linarith only [h0, h1, h1052, h1163, h1165, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1167 | h1167
                                · linarith only [h0, h1, h1163, h1167, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1169 | h1169
                                  · linarith only [h1054, h1158, h1169, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1171 | h1171
                                    · linarith only [h1138, h1158, h1169, h1171, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1173 | h1173
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1174 | h1174
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1175 | h1175
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1176 | h1176
                                            · linarith only [h1021, h1169, h1173, h1176, h845, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                                            · linarith only [h1022, h1176, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                          · linarith only [h1021, h1174, h1175, h845, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u6ehi10]
                                        · linarith only [h1021, h1173, h1174, h845, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi7]
                                      · linarith only [h1, h1021, h1159, h1173, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi7]
                        · linarith only [h1160, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1183 | h1183
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1184 | h1184
                          · linarith only [h1022, h1184, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1186 | h1186
                            · linarith only [h0, h1050, h1186, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1188 | h1188
                              · linarith only [h0, h1, h1052, h1159, h1188, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1190 | h1190
                                · linarith only [h0, h1, h1159, h1190, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi8]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1192 | h1192
                                  · linarith only [h1054, h1158, h1192, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1194 | h1194
                                    · linarith only [h1138, h1158, h1192, h1194, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1196 | h1196
                                      · linarith only [h1, h1159, h1186, h1196, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                                      · linarith only [h0, h1, h1196, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                        · linarith only [h1183, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h1158, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
        · linarith only [h1021, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi6, u6elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1202 | h1202
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1203 | h1203
      · rcases m.htr 0 1 6 (by decide) (by decide) with h1204 | h1204
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1205 | h1205
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1206 | h1206
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1207 | h1207
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1208 | h1208
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1209 | h1209
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1210 | h1210
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1211 | h1211
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1212 | h1212
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1213 | h1213
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1214 | h1214
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1215 | h1215
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1216 | h1216
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1217 | h1217
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1218 | h1218
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1219 | h1219
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1220 | h1220
                                        · linarith only [h1202, h1220, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · linarith only [h1219, h1220, hc45, hlam, hphi, ht56, u6elo4]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1223 | h1223
                                        · linarith only [h0, h1202, h1211, h1219, h1223, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1225 | h1225
                                          · linarith only [h0, h1203, h1225, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1227 | h1227
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1228 | h1228
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1229 | h1229
                                                · linarith only [h1205, h1229, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                                                · linarith only [h1205, h1210, h1227, h1229, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                              · linarith only [h1205, h1209, h1227, h1228, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                            · linarith only [h0, h1202, h1211, h1212, h1217, h1219, h1225, h1227, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                    · linarith only [h1205, h1209, h1217, h1218, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1235 | h1235
                                    · linarith only [h1205, h1208, h1217, h1235, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1237 | h1237
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1238 | h1238
                                        · linarith only [h0, h1202, h1238, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi10]
                                        · linarith only [h1237, h1238, hc45, hlam, hphi, ht56, u6elo4]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1241 | h1241
                                        · linarith only [h0, h1202, h1211, h1237, h1241, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1243 | h1243
                                          · linarith only [h0, h1203, h1243, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1245 | h1245
                                            · linarith only [h0, h1202, h1211, h1212, h1213, h1217, h1237, h1243, h1245, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1247 | h1247
                                              · linarith only [h0, h1202, h1211, h1212, h1213, h1217, h1237, h1243, h1247, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1249 | h1249
                                                · linarith only [h0, h1202, h1211, h1212, h1213, h1217, h1237, h1243, h1249, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1251 | h1251
                                                  · linarith only [h0, h1202, h1211, h1212, h1214, h1237, h1243, h1251, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                                  · rcases m.htr 2 4 6 (by decide) (by decide) with h1253 | h1253
                                                    · linarith only [h0, h1202, h1211, h1212, h1214, h1237, h1241, h1243, h1253, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                                                    · rcases m.htr 2 5 6 (by decide) (by decide) with h1255 | h1255
                                                      · linarith only [h1215, h1243, h1255, hlam]
                                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1257 | h1257
                                                        · linarith only [h1205, h1208, h1217, h1237, h1257, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                                        · linarith only [h0, h1202, h1211, h1213, h1217, h1257, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                · linarith only [h0, h1202, h1211, h1212, h1216, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                              · linarith only [h0, h1202, h1211, h1212, h1215, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                            · linarith only [h0, h1202, h1211, h1212, h1214, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                          · linarith only [h0, h1202, h1211, h1212, h1213, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                        · linarith only [h1212, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1265 | h1265
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1266 | h1266
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1267 | h1267
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1268 | h1268
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1269 | h1269
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1270 | h1270
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1271 | h1271
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1272 | h1272
                                      · linarith only [h1202, h1211, h1272, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1274 | h1274
                                        · linarith only [h0, h1203, h1272, h1274, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1276 | h1276
                                          · linarith only [h0, h1203, h1276, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1278 | h1278
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1279 | h1279
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1280 | h1280
                                                · linarith only [h1205, h1280, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                                                · linarith only [h1205, h1210, h1278, h1280, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                              · linarith only [h1205, h1209, h1278, h1279, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                            · linarith only [h1265, h1270, h1272, h1276, h1278, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo4]
                                    · linarith only [h1205, h1209, h1270, h1271, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1286 | h1286
                                    · linarith only [h1205, h1208, h1270, h1286, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1288 | h1288
                                      · linarith only [h1211, h1288, hc14, hlam, hphi, ht01, u0ehi9]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1290 | h1290
                                        · linarith only [h0, h1202, h1290, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1292 | h1292
                                          · linarith only [h1205, h1209, h1286, h1292, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1294 | h1294
                                            · linarith only [h0, h1203, h1265, h1266, h1270, h1288, h1292, h1294, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1296 | h1296
                                              · linarith only [h0, h1203, h1265, h1266, h1270, h1288, h1292, h1296, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1298 | h1298
                                                · linarith only [h0, h1203, h1265, h1266, h1270, h1288, h1292, h1298, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1300 | h1300
                                                  · linarith only [h1211, h1300, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                                                  · rcases m.htr 2 4 6 (by decide) (by decide) with h1302 | h1302
                                                    · linarith only [h1206, h1302, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi10]
                                                    · rcases m.htr 2 5 6 (by decide) (by decide) with h1304 | h1304
                                                      · linarith only [h1268, h1292, h1304, hlam]
                                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1306 | h1306
                                                        · linarith only [h1211, h1306, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                                                        · rcases m.htr 3 4 6 (by decide) (by decide) with h1308 | h1308
                                                          · linarith only [h1205, h1209, h1290, h1306, h1308, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                                                          · linarith only [h1266, h1270, h1308, hc23, hlam, hphi, ht34, ht45, ht56, u6elo4]
                                · linarith only [h0, h1203, h1265, h1269, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                              · linarith only [h0, h1203, h1265, h1268, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                            · linarith only [h0, h1203, h1265, h1267, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                          · linarith only [h0, h1203, h1265, h1266, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                        · linarith only [h1265, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h1209, h1210, hc35, hlam, hphi, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1317 | h1317
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1318 | h1318
                      · linarith only [h1208, h1209, h1318, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1320 | h1320
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1321 | h1321
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1322 | h1322
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1323 | h1323
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1324 | h1324
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1325 | h1325
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1326 | h1326
                                    · linarith only [h1208, h1209, h1326, hc13, hlam, hphi, ht01, u0ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1328 | h1328
                                      · linarith only [h1203, h1318, h1325, h1326, h1328, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1330 | h1330
                                        · linarith only [h0, h1203, h1325, h1326, h1330, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1332 | h1332
                                          · linarith only [h0, h1203, h1332, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                                          · linarith only [h1325, h1326, h1332, hc34, hlam, hphi, ht45, ht56, u6elo5]
                                  · linarith only [h1208, h1209, h1321, h1325, hc23, hc35, hlam, hphi]
                                · linarith only [h0, h1204, h1324, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                              · linarith only [h0, h1203, h1209, h1317, h1323, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                            · linarith only [h0, h1203, h1209, h1317, h1322, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                          · linarith only [h0, h1203, h1209, h1317, h1321, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                        · linarith only [h1209, h1317, h1320, hlam, hphi, u6ehi9, u6elo5]
                    · linarith only [h1208, h1317, hc34, hlam, hphi, ht45, ht56, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1342 | h1342
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1343 | h1343
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1344 | h1344
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1345 | h1345
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1346 | h1346
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1347 | h1347
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1348 | h1348
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1349 | h1349
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1350 | h1350
                                  · linarith only [h1208, h1342, h1345, h1350, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1352 | h1352
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1353 | h1353
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1354 | h1354
                                        · linarith only [h1202, h1354, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi10]
                                        · linarith only [h1350, h1352, h1354, hc35, hlam, hphi, ht56, u6elo4]
                                      · linarith only [h1344, h1350, h1352, h1353, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo3]
                                    · linarith only [h1208, h1342, h1346, h1352, hc23, hc34, hlam, hphi]
                                · linarith only [h0, h1204, h1349, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                              · linarith only [h0, h1202, h1208, h1342, h1345, h1348, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                            · linarith only [h0, h1202, h1208, h1342, h1345, h1347, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                          · linarith only [h0, h1202, h1208, h1342, h1345, h1346, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                        · linarith only [h1345, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h1208, h1342, h1344, hlam]
                    · linarith only [h1342, h1343, hc35, hlam, hphi, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1366 | h1366
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1367 | h1367
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1368 | h1368
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1369 | h1369
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1370 | h1370
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1371 | h1371
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1372 | h1372
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1373 | h1373
                                  · linarith only [h1208, h1366, h1373, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1375 | h1375
                                    · linarith only [h1202, h1342, h1366, h1373, h1375, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1377 | h1377
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1378 | h1378
                                        · linarith only [h0, h1202, h1378, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi10]
                                        · linarith only [h1377, h1378, hc45, hlam, hphi, ht56, u6elo4]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1381 | h1381
                                        · linarith only [h0, h1202, h1367, h1377, h1381, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1383 | h1383
                                          · linarith only [h0, h1203, h1383, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1385 | h1385
                                            · linarith only [h0, h1202, h1367, h1368, h1369, h1373, h1377, h1383, h1385, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1387 | h1387
                                              · linarith only [h0, h1202, h1342, h1366, h1367, h1368, h1369, h1373, h1377, h1383, h1387, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1389 | h1389
                                                · linarith only [h0, h1202, h1367, h1368, h1369, h1373, h1377, h1383, h1389, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                                                · linarith only [h1208, h1366, h1389, hc23, hc34, hlam, hphi]
                                · linarith only [h0, h1202, h1367, h1368, h1372, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                              · linarith only [h0, h1202, h1342, h1366, h1367, h1371, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                            · linarith only [h0, h1202, h1342, h1366, h1367, h1370, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                          · linarith only [h0, h1202, h1342, h1366, h1367, h1369, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                        · linarith only [h1342, h1366, h1368, hlam, hphi, u6ehi9, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1397 | h1397
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1398 | h1398
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1399 | h1399
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1400 | h1400
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1401 | h1401
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1402 | h1402
                                  · linarith only [h1208, h1366, h1402, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1404 | h1404
                                    · linarith only [h1342, h1366, h1404, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1406 | h1406
                                      · linarith only [h1202, h1208, h1366, h1367, h1406, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi9]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1408 | h1408
                                        · linarith only [h0, h1203, h1406, h1408, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1410 | h1410
                                          · linarith only [h0, h1203, h1410, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1412 | h1412
                                            · linarith only [h0, h1203, h1397, h1398, h1402, h1406, h1410, h1412, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1414 | h1414
                                              · linarith only [h0, h1203, h1342, h1366, h1397, h1398, h1402, h1406, h1410, h1414, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1416 | h1416
                                                · linarith only [h0, h1203, h1397, h1398, h1402, h1406, h1410, h1416, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                                · linarith only [h1208, h1366, h1416, hc23, hc34, hlam, hphi]
                                · linarith only [h0, h1203, h1397, h1401, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                              · linarith only [h0, h1203, h1208, h1366, h1367, h1400, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                            · linarith only [h0, h1203, h1208, h1366, h1367, h1399, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                          · linarith only [h0, h1203, h1208, h1366, h1367, h1398, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                        · linarith only [h1208, h1366, h1367, h1397, hlam, hphi, u6ehi9, u6elo5]
                    · linarith only [h1366, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
              · linarith only [h0, h1203, h1207, hlam]
            · linarith only [h0, h1202, h1206, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1427 | h1427
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1428 | h1428
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1429 | h1429
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1430 | h1430
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1431 | h1431
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1432 | h1432
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1433 | h1433
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1434 | h1434
                          · linarith only [h0, h1202, h1205, h1432, h1433, h1434, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                          · linarith only [h0, h1202, h1432, h1433, h1434, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                        · linarith only [h1433, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1438 | h1438
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1439 | h1439
                          · linarith only [h0, h1204, h1205, h1439, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                          · linarith only [h0, h1203, h1438, h1439, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                        · linarith only [h1432, h1438, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi9, u6elo5]
                    · linarith only [h1429, h1431, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · linarith only [h0, h1203, h1205, h1430, hlam]
                · linarith only [h0, h1202, h1205, h1429, hlam]
              · linarith only [h0, h1203, h1428, hlam]
            · linarith only [h0, h1202, h1427, hlam]
        · linarith only [h1202, h1204, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi9, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h1449 | h1449
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1450 | h1450
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1451 | h1451
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1452 | h1452
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1453 | h1453
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1454 | h1454
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1455 | h1455
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1456 | h1456
                      · linarith only [h1202, h1203, h1456, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1458 | h1458
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1459 | h1459
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1460 | h1460
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1461 | h1461
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1462 | h1462
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1463 | h1463
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1464 | h1464
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1465 | h1465
                                      · linarith only [h1202, h1456, h1465, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1467 | h1467
                                        · linarith only [h1202, h1203, h1465, h1467, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1469 | h1469
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1470 | h1470
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1471 | h1471
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1472 | h1472
                                                · linarith only [h1450, h1472, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                                                · linarith only [h1471, h1472, hc35, hlam, hphi, ht56, u6elo3]
                                              · linarith only [h1450, h1454, h1470, h1471, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                            · linarith only [h1203, h1449, h1462, h1463, h1465, h1467, h1470, hc23, hc45, hlam, hphi, ht34, u6ehi8, u6elo4]
                                          · linarith only [h1203, h1449, h1462, h1469, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u6ehi8]
                                    · linarith only [h1450, h1454, h1463, h1464, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1479 | h1479
                                    · linarith only [h1450, h1453, h1463, h1479, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                    · linarith only [h1202, h1203, h1450, h1454, h1479, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                · linarith only [h1202, h1203, h1461, h1462, hc26, hlam, hphi, ht01, ht12, u0ehi9]
                              · linarith only [h0, h1202, h1461, hc25, hlam, hphi, ht01, ht12, u0ehi9]
                            · linarith only [h0, h1202, h1460, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                          · linarith only [h0, h1202, h1459, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                        · linarith only [h1458, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h1453, h1455, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1488 | h1488
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1489 | h1489
                      · linarith only [h1202, h1203, h1489, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1491 | h1491
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1492 | h1492
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1493 | h1493
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1494 | h1494
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1495 | h1495
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1496 | h1496
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1497 | h1497
                                    · linarith only [h1454, h1488, h1497, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1499 | h1499
                                      · linarith only [h1202, h1489, h1499, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1501 | h1501
                                        · linarith only [h1202, h1203, h1499, h1501, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1503 | h1503
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1504 | h1504
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1505 | h1505
                                              · linarith only [h1450, h1497, h1505, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1507 | h1507
                                                · linarith only [h1452, h1505, h1507, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                                                · linarith only [h1454, h1488, h1507, hc23, hc35, hlam, hphi]
                                            · linarith only [h1453, h1454, h1504, hc23, hc35, hlam, hphi]
                                          · linarith only [h1203, h1449, h1495, h1503, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u6ehi8]
                                  · linarith only [h1453, h1454, h1496, hc13, hc35, hlam, hphi]
                                · linarith only [h0, h1495, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h0, h1449, h1452, h1494, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                            · linarith only [h0, h1449, h1493, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                          · linarith only [h0, h1449, h1492, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1491, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h1453, h1488, hc34, hlam, hphi, ht45, ht56, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1519 | h1519
                  · linarith only [h1202, h1203, h1453, h1519, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1521 | h1521
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1522 | h1522
                      · linarith only [h1202, h1203, h1522, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1524 | h1524
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1525 | h1525
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1526 | h1526
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1527 | h1527
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1528 | h1528
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1529 | h1529
                                  · linarith only [h1453, h1521, h1529, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1531 | h1531
                                    · linarith only [h1519, h1521, h1531, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1533 | h1533
                                      · linarith only [h1202, h1203, h1453, h1521, h1522, h1531, h1533, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi9]
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1535 | h1535
                                        · linarith only [h1202, h1203, h1533, h1535, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi10]
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1537 | h1537
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1538 | h1538
                                            · linarith only [h1453, h1521, h1538, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1540 | h1540
                                              · linarith only [h1525, h1529, h1535, h1540, hc35, hlam, hphi, ht56, u6elo4]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1542 | h1542
                                                · linarith only [h1525, h1529, h1535, h1542, hlam, hphi, u6ehi9, u6elo4]
                                                · linarith only [h1453, h1521, h1542, hc23, hc34, hlam, hphi]
                                          · linarith only [h1202, h1203, h1453, h1521, h1537, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u6ehi9]
                                · linarith only [h1203, h1527, h1528, hc26, hlam, hphi, ht01, ht12, u0ehi6]
                              · linarith only [h0, h1452, h1527, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h0, h1202, h1453, h1521, h1526, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                          · linarith only [h0, h1202, h1453, h1521, h1525, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                        · linarith only [h1524, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h1521, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1552 | h1552
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1553 | h1553
                  · linarith only [h1450, h1452, h1553, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1555 | h1555
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1556 | h1556
                      · linarith only [h0, h1202, h1452, h1556, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1558 | h1558
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1559 | h1559
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1560 | h1560
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1561 | h1561
                              · linarith only [h1450, h1452, h1555, h1561, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                              · linarith only [h0, h1449, h1561, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                            · linarith only [h0, h1449, h1560, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                          · linarith only [h0, h1449, h1450, h1559, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                        · linarith only [h1558, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h1552, h1555, hc34, hlam, hphi, ht45, ht56, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1568 | h1568
                  · linarith only [h1450, h1452, h1568, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1570 | h1570
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1571 | h1571
                      · linarith only [h0, h1202, h1452, h1571, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1573 | h1573
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1574 | h1574
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1575 | h1575
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1576 | h1576
                              · linarith only [h0, h1449, h1452, h1576, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                              · linarith only [h0, h1202, h1552, h1570, h1576, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                            · linarith only [h0, h1202, h1552, h1570, h1575, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                          · linarith only [h0, h1202, h1450, h1552, h1570, h1574, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                        · linarith only [h1573, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h1570, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
            · linarith only [h0, h1202, h1451, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1584 | h1584
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1585 | h1585
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1586 | h1586
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1587 | h1587
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1588 | h1588
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1589 | h1589
                      · linarith only [h1202, h1203, h1589, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1591 | h1591
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1592 | h1592
                          · linarith only [h1203, h1449, h1450, h1585, h1592, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                          · linarith only [h0, h1449, h1592, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1203, h1449, h1591, hlam, hphi, u6ehi7, u6elo5]
                    · linarith only [h1203, h1449, h1450, h1585, h1588, hlam, hphi, u6ehi7, u6elo3]
                  · linarith only [h1450, h1585, h1587, hlam]
                · linarith only [h1202, h1203, h1450, h1585, h1586, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1599 | h1599
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1600 | h1600
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1601 | h1601
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1602 | h1602
                      · linarith only [h0, h1202, h1585, h1602, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1604 | h1604
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1605 | h1605
                          · linarith only [h0, h1202, h1450, h1605, hc12, hlam, hphi, ht01, u0ehi9]
                          · linarith only [h0, h1202, h1605, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                        · linarith only [h0, h1202, h1585, h1604, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi9, u6elo5]
                    · linarith only [h0, h1449, h1585, h1600, h1601, hlam, hphi, u6ehi7, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1610 | h1610
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1611 | h1611
                      · linarith only [h1202, h1203, h1611, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1613 | h1613
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1614 | h1614
                          · linarith only [h0, h1449, h1450, h1614, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                          · linarith only [h0, h1449, h1614, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h0, h1449, h1450, h1600, h1613, hlam, hphi, u6ehi7, u6elo5]
                    · linarith only [h0, h1449, h1450, h1610, hlam, hphi, u6ehi7, u6elo3]
                · linarith only [h0, h1202, h1450, h1599, hlam]
            · linarith only [h0, h1202, h1584, hlam]
        · linarith only [h1202, h1449, hc14, hlam, hphi, ht45, ht56, u6elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1622 | h1622
      · rcases m.htr 0 1 6 (by decide) (by decide) with h1623 | h1623
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1624 | h1624
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1625 | h1625
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1626 | h1626
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1627 | h1627
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1628 | h1628
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1629 | h1629
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1630 | h1630
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1631 | h1631
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1632 | h1632
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1633 | h1633
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1634 | h1634
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1635 | h1635
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1636 | h1636
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1637 | h1637
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1638 | h1638
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1639 | h1639
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1640 | h1640
                                          · linarith only [h1622, h1640, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1642 | h1642
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1643 | h1643
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1644 | h1644
                                                · linarith only [h1624, h1644, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                                                · linarith only [h1642, h1644, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                              · linarith only [h1624, h1628, h1642, h1643, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1648 | h1648
                                              · linarith only [h1624, h1627, h1642, h1648, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                              · linarith only [h1202, h1622, h1631, h1632, h1636, h1637, h1640, h1648, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                                        · linarith only [h1202, h1622, h1631, h1639, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi11]
                                      · linarith only [h1202, h1622, h1630, h1631, h1638, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi11]
                                    · linarith only [h1202, h1622, h1631, h1636, h1637, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi11]
                                  · linarith only [h1202, h1622, h1624, h1627, h1631, h1636, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi11]
                                · linarith only [h1202, h1622, h1631, h1633, h1635, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                              · linarith only [h1202, h1622, h1631, h1633, h1634, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                            · linarith only [h0, h1622, h1631, h1633, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                          · linarith only [h0, h1622, h1631, h1632, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                        · linarith only [h1631, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h1202, h1622, h1630, hlam]
                    · linarith only [h1627, h1629, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · linarith only [h1202, h1622, h1627, h1628, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1663 | h1663
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1664 | h1664
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1665 | h1665
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1666 | h1666
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1667 | h1667
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1668 | h1668
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1669 | h1669
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1670 | h1670
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1671 | h1671
                                  · linarith only [h1627, h1664, h1671, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1673 | h1673
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1674 | h1674
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1675 | h1675
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1676 | h1676
                                          · linarith only [h1622, h1676, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi11]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1678 | h1678
                                            · linarith only [h1202, h1624, h1671, h1678, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1680 | h1680
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1681 | h1681
                                                · linarith only [h1625, h1678, h1681, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                                                · linarith only [h1627, h1664, h1681, hc23, hc34, hlam, hphi]
                                              · linarith only [h1627, h1663, h1680, hc23, hc34, hlam, hphi]
                                        · linarith only [h1202, h1622, h1666, h1675, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi11]
                                      · linarith only [h1202, h1622, h1666, h1674, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi11]
                                    · linarith only [h1627, h1663, h1673, hc13, hc34, hlam, hphi]
                                · linarith only [h1202, h1622, h1666, h1668, h1670, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                              · linarith only [h1202, h1622, h1666, h1668, h1669, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                            · linarith only [h0, h1622, h1625, h1666, h1668, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi11]
                          · linarith only [h0, h1622, h1666, h1667, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                        · linarith only [h1666, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h1202, h1622, h1665, hlam]
                    · linarith only [h1663, h1664, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1695 | h1695
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1696 | h1696
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1697 | h1697
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1698 | h1698
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1699 | h1699
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1700 | h1700
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1701 | h1701
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1702 | h1702
                                  · linarith only [h1627, h1695, h1702, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1704 | h1704
                                    · linarith only [h1663, h1695, h1702, h1704, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1706 | h1706
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1707 | h1707
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1708 | h1708
                                          · linarith only [h1202, h1622, h1702, h1708, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi11]
                                          · linarith only [h1202, h1622, h1697, h1702, h1704, h1708, hc13, hc34, hlam, hphi]
                                        · linarith only [h1202, h1623, h1707, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi7]
                                      · linarith only [h1202, h1622, h1663, h1695, h1706, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi9]
                                · linarith only [h0, h1622, h1663, h1695, h1701, hlam, hphi, u6ehi9, u6elo2]
                              · linarith only [h1202, h1622, h1663, h1695, h1699, h1700, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                            · linarith only [h0, h1622, h1625, h1663, h1695, h1699, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                          · linarith only [h0, h1622, h1663, h1695, h1698, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                        · linarith only [h1663, h1695, h1697, hlam, hphi, u6ehi9, u6elo5]
                      · linarith only [h1202, h1622, h1696, hlam]
                    · linarith only [h1695, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
              · linarith only [h0, h1622, h1626, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1721 | h1721
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1722 | h1722
                · linarith only [h1624, h1625, h1722, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1724 | h1724
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1725 | h1725
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1726 | h1726
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1727 | h1727
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1728 | h1728
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1729 | h1729
                            · linarith only [h0, h1622, h1625, h1727, h1729, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                            · linarith only [h0, h1622, h1727, h1729, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                          · linarith only [h0, h1622, h1624, h1727, h1728, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi11]
                        · linarith only [h1727, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h0, h1622, h1625, h1726, hlam]
                    · linarith only [h1724, h1725, hc35, hlam, hphi, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1736 | h1736
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1737 | h1737
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1738 | h1738
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1739 | h1739
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1740 | h1740
                            · linarith only [h0, h1622, h1625, h1724, h1736, h1740, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                            · linarith only [h0, h1622, h1724, h1736, h1740, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi9]
                          · linarith only [h0, h1622, h1624, h1724, h1736, h1739, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                        · linarith only [h1724, h1736, h1738, hlam, hphi, u6ehi9, u6elo5]
                      · linarith only [h0, h1622, h1625, h1737, hlam]
                    · linarith only [h1736, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
              · linarith only [h0, h1622, h1721, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1748 | h1748
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1749 | h1749
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1750 | h1750
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1751 | h1751
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1752 | h1752
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1753 | h1753
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1754 | h1754
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1755 | h1755
                          · linarith only [h1202, h1622, h1624, h1748, h1754, h1755, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                          · linarith only [h0, h1622, h1754, h1755, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                        · linarith only [h1754, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h1202, h1622, h1753, hlam]
                    · linarith only [h1750, h1752, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · linarith only [h0, h1622, h1624, h1751, hlam]
                · linarith only [h1624, h1748, h1750, hlam]
              · linarith only [h1202, h1622, h1748, h1749, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1764 | h1764
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1765 | h1765
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1766 | h1766
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1767 | h1767
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1768 | h1768
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1769 | h1769
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1770 | h1770
                          · linarith only [h1624, h1770, hc12, hlam, hphi, ht01, u0ehi7]
                          · linarith only [h0, h1622, h1769, h1770, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                        · linarith only [h1769, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h0, h1622, h1748, h1768, hlam]
                    · linarith only [h0, h1623, h1748, h1765, h1767, hlam, hphi, u6ehi7, u6elo3]
                  · linarith only [h0, h1622, h1748, h1765, h1766, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1777 | h1777
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1778 | h1778
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1779 | h1779
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1780 | h1780
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1781 | h1781
                          · linarith only [h0, h1622, h1624, h1780, h1781, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                          · linarith only [h0, h1622, h1780, h1781, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi11]
                        · linarith only [h1780, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h0, h1622, h1624, h1765, h1779, hlam]
                    · linarith only [h0, h1623, h1624, h1778, hlam, hphi, u6ehi7, u6elo3]
                  · linarith only [h0, h1622, h1624, h1777, hlam]
              · linarith only [h0, h1622, h1764, hlam]
        · linarith only [h1623, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi6, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h1790 | h1790
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1791 | h1791
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1792 | h1792
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1793 | h1793
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1794 | h1794
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1795 | h1795
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1796 | h1796
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1797 | h1797
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1798 | h1798
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1799 | h1799
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1800 | h1800
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1801 | h1801
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1802 | h1802
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1803 | h1803
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1804 | h1804
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1805 | h1805
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1806 | h1806
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1807 | h1807
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1808 | h1808
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1809 | h1809
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1810 | h1810
                                                · linarith only [h1791, h1810, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                                                · linarith only [h1808, h1810, hc34, hlam, hphi, ht45, ht56, u6elo3]
                                              · linarith only [h1795, h1808, h1809, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1814 | h1814
                                              · linarith only [h1791, h1794, h1808, h1814, hc35, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1816 | h1816
                                                · linarith only [h1791, h1794, h1808, h1816, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1818 | h1818
                                                  · rcases m.htr 2 4 6 (by decide) (by decide) with h1819 | h1819
                                                    · linarith only [h1792, h1819, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi10]
                                                    · linarith only [h1818, h1819, hc45, hlam, hphi, ht56, u6elo4]
                                                  · rcases m.htr 2 4 6 (by decide) (by decide) with h1822 | h1822
                                                    · linarith only [h1791, h1794, h1797, h1818, h1822, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi10]
                                                    · rcases m.htr 2 5 6 (by decide) (by decide) with h1824 | h1824
                                                      · linarith only [h1793, h1824, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi11]
                                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1826 | h1826
                                                        · linarith only [h1791, h1794, h1808, h1818, h1826, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                                        · linarith only [h1791, h1794, h1797, h1808, h1826, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                          · linarith only [h1622, h1790, h1807, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u6ehi7]
                                        · linarith only [h1622, h1790, h1802, h1805, h1806, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi8]
                                      · linarith only [h1202, h1790, h1791, h1794, h1797, h1802, h1805, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi8]
                                    · linarith only [h1202, h1790, h1791, h1795, h1802, h1803, h1804, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi8]
                                  · linarith only [h1202, h1790, h1791, h1794, h1802, h1803, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi8]
                                · linarith only [h0, h1802, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1202, h1790, h1800, h1801, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                            · linarith only [h0, h1790, h1800, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h1799, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1798, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1839 | h1839
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1840 | h1840
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1841 | h1841
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1842 | h1842
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1843 | h1843
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1844 | h1844
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1845 | h1845
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1846 | h1846
                                      · linarith only [h1202, h1790, h1797, h1840, h1843, h1844, h1846, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi8]
                                      · linarith only [h1202, h1790, h1843, h1846, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi8]
                                    · linarith only [h1791, h1795, h1844, h1845, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                  · linarith only [h1202, h1790, h1791, h1794, h1843, h1844, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi8]
                                · linarith only [h0, h1843, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1202, h1790, h1793, h1841, h1842, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                            · linarith only [h0, h1790, h1792, h1841, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                          · linarith only [h0, h1790, h1840, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1839, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h1794, h1796, hc34, hlam, hphi, ht45, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1857 | h1857
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1858 | h1858
                      · linarith only [h1794, h1795, h1858, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1860 | h1860
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1861 | h1861
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1862 | h1862
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1863 | h1863
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1864 | h1864
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1865 | h1865
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1866 | h1866
                                    · linarith only [h1202, h1790, h1794, h1795, h1861, h1864, h1866, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi8]
                                    · linarith only [h1202, h1790, h1864, h1865, h1866, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi8]
                                  · linarith only [h1794, h1795, h1865, hc13, hc35, hlam, hphi]
                                · linarith only [h0, h1864, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1202, h1790, h1793, h1862, h1863, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                            · linarith only [h0, h1790, h1792, h1862, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                          · linarith only [h0, h1790, h1791, h1861, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                        · linarith only [h1795, h1857, h1860, hlam, hphi, u6ehi9, u6elo5]
                    · linarith only [h1202, h1790, h1794, h1857, hlam, hphi, u6ehi7, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1876 | h1876
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1877 | h1877
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1878 | h1878
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1879 | h1879
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1880 | h1880
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1881 | h1881
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1882 | h1882
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1883 | h1883
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1884 | h1884
                                  · linarith only [h1622, h1790, h1794, h1876, h1883, h1884, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi8]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1886 | h1886
                                    · linarith only [h1622, h1790, h1883, h1884, h1886, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi8]
                                    · linarith only [h1794, h1876, h1886, hc13, hc34, hlam, hphi]
                                · linarith only [h1202, h1790, h1881, h1883, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                              · linarith only [h1202, h1790, h1793, h1881, h1882, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                            · linarith only [h0, h1790, h1792, h1881, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                          · linarith only [h0, h1790, h1791, h1880, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                        · linarith only [h1622, h1790, h1879, hlam, hphi, u6ehi7, u6elo5]
                      · linarith only [h1794, h1876, h1878, hlam]
                    · linarith only [h1622, h1790, h1876, h1877, hlam, hphi, u6ehi7, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1896 | h1896
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1897 | h1897
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1898 | h1898
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1899 | h1899
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1900 | h1900
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1901 | h1901
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1902 | h1902
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1903 | h1903
                                  · linarith only [h1794, h1896, h1903, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1905 | h1905
                                    · linarith only [h1876, h1896, h1905, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1907 | h1907
                                      · rcases m.htr 1 4 6 (by decide) (by decide) with h1908 | h1908
                                        · rcases m.htr 1 5 6 (by decide) (by decide) with h1909 | h1909
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1910 | h1910
                                            · linarith only [h1791, h1903, h1910, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1912 | h1912
                                              · linarith only [h1622, h1790, h1899, h1902, h1905, h1912, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi8]
                                              · rcases m.htr 2 3 6 (by decide) (by decide) with h1914 | h1914
                                                · linarith only [h1792, h1910, h1914, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi9]
                                                · linarith only [h1794, h1896, h1914, hc23, hc34, hlam, hphi]
                                          · linarith only [h1622, h1790, h1902, h1909, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u6ehi8]
                                        · linarith only [h1622, h1790, h1902, h1907, h1908, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi8]
                                      · linarith only [h1202, h1790, h1897, h1902, h1907, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi8]
                                · linarith only [h1202, h1790, h1900, h1902, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                              · linarith only [h1202, h1790, h1793, h1900, h1901, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                            · linarith only [h0, h1790, h1792, h1900, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                          · linarith only [h0, h1790, h1899, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1622, h1790, h1898, hlam, hphi, u6ehi7, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1925 | h1925
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1926 | h1926
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1927 | h1927
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1928 | h1928
                              · rcases m.htr 1 2 6 (by decide) (by decide) with h1929 | h1929
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1930 | h1930
                                  · linarith only [h1794, h1896, h1930, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1932 | h1932
                                    · linarith only [h1876, h1896, h1932, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1934 | h1934
                                      · linarith only [h1202, h1790, h1897, h1927, h1929, h1934, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi8]
                                      · linarith only [h1202, h1790, h1929, h1934, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi8]
                                · linarith only [h0, h1929, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                              · linarith only [h1202, h1790, h1793, h1927, h1928, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                            · linarith only [h0, h1790, h1792, h1927, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                          · linarith only [h0, h1790, h1791, h1926, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                        · linarith only [h1202, h1790, h1897, h1925, hlam, hphi, u6ehi7, u6elo5]
                    · linarith only [h1896, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1943 | h1943
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1944 | h1944
                  · linarith only [h1791, h1793, h1944, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1946 | h1946
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1947 | h1947
                      · linarith only [h1792, h1793, h1947, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1949 | h1949
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1950 | h1950
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1951 | h1951
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1952 | h1952
                              · linarith only [h1791, h1793, h1946, h1952, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                              · linarith only [h0, h1790, h1952, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                            · linarith only [h0, h1790, h1792, h1951, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                          · linarith only [h0, h1790, h1791, h1793, h1950, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1949, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h1202, h1790, h1943, h1946, hlam, hphi, u6ehi7, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1959 | h1959
                  · linarith only [h1791, h1793, h1959, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1961 | h1961
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1962 | h1962
                      · linarith only [h1792, h1793, h1962, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1964 | h1964
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1965 | h1965
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1966 | h1966
                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1967 | h1967
                              · linarith only [h1202, h1790, h1792, h1793, h1967, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                              · linarith only [h0, h1790, h1967, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                            · linarith only [h0, h1790, h1792, h1966, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                          · linarith only [h0, h1790, h1791, h1793, h1965, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1964, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                    · linarith only [h1961, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1974 | h1974
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1975 | h1975
                · linarith only [h1791, h1792, h1975, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1977 | h1977
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1978 | h1978
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1979 | h1979
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1980 | h1980
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1981 | h1981
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1982 | h1982
                            · linarith only [h1791, h1792, h1978, h1982, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                            · linarith only [h0, h1790, h1982, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h1791, h1981, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                        · linarith only [h1622, h1790, h1980, hlam, hphi, u6ehi7, u6elo5]
                      · linarith only [h1791, h1792, h1977, h1979, hlam]
                    · linarith only [h1622, h1790, h1977, h1978, hlam, hphi, u6ehi7, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h1989 | h1989
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h1990 | h1990
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1991 | h1991
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1992 | h1992
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1993 | h1993
                            · linarith only [h1792, h1993, hc12, hlam, hphi, ht01, u0ehi7]
                            · linarith only [h0, h1790, h1993, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h1791, h1992, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                        · linarith only [h1622, h1790, h1991, hlam, hphi, u6ehi7, u6elo5]
                      · linarith only [h1792, h1974, h1990, hlam]
                    · linarith only [h1989, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2000 | h2000
                · linarith only [h1791, h1792, h2000, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2002 | h2002
                  · linarith only [h1791, h1974, h2002, hlam]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h2004 | h2004
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h2005 | h2005
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2006 | h2006
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2007 | h2007
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h2008 | h2008
                            · linarith only [h1791, h1792, h2004, h2008, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi9]
                            · linarith only [h0, h1790, h2008, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h1791, h2007, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi7]
                        · linarith only [h1791, h1974, h2006, hc23, hlam, hphi, ht34, ht45, ht56, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2013 | h2013
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2014 | h2014
                          · rcases m.htr 1 2 4 (by decide) (by decide) with h2015 | h2015
                            · linarith only [h0, h1790, h1792, h2015, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                            · linarith only [h0, h1790, h2015, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h2014, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h0, h1790, h1792, h2005, h2013, hlam, hphi, u6ehi7, u6elo5]
                    · linarith only [h2004, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi8, u6elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2021 | h2021
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2022 | h2022
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2023 | h2023
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2024 | h2024
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h2025 | h2025
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h2026 | h2026
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2027 | h2027
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2028 | h2028
                          · linarith only [h1622, h1790, h1791, h2021, h2026, h2028, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h2028, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1622, h1790, h2027, hlam, hphi, u6ehi7, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2032 | h2032
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2033 | h2033
                          · linarith only [h1791, h2033, hc12, hlam, hphi, ht01, u0ehi7]
                          · linarith only [h0, h1790, h2033, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1202, h1790, h2026, h2032, hlam, hphi, u6ehi7, u6elo5]
                    · linarith only [h1622, h1790, h1791, h2022, h2025, hlam, hphi, u6ehi7, u6elo3]
                  · linarith only [h1791, h2022, h2024, hlam]
                · linarith only [h1791, h2021, h2023, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2040 | h2040
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2041 | h2041
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h2042 | h2042
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h2043 | h2043
                      · linarith only [h2021, h2022, h2043, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2045 | h2045
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2046 | h2046
                          · linarith only [h1202, h1790, h1791, h2021, h2046, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h2046, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1202, h1790, h2021, h2022, h2045, hlam, hphi, u6ehi7, u6elo5]
                    · linarith only [h1202, h1790, h2021, h2022, h2041, h2042, hlam, hphi, u6ehi7, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h2051 | h2051
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h2052 | h2052
                      · linarith only [h1791, h2021, h2041, h2052, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2054 | h2054
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2055 | h2055
                          · linarith only [h1202, h1790, h1791, h2021, h2055, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h2055, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1202, h1790, h1791, h2021, h2041, h2054, hlam, hphi, u6ehi7, u6elo5]
                    · linarith only [h1202, h1790, h1791, h2021, h2051, hlam, hphi, u6ehi7, u6elo3]
                · linarith only [h1791, h2021, h2040, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2061 | h2061
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2062 | h2062
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2063 | h2063
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h2064 | h2064
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h2065 | h2065
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2066 | h2066
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2067 | h2067
                          · linarith only [h1791, h2061, h2066, h2067, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi11]
                          · linarith only [h0, h1790, h2067, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1622, h1790, h2066, hlam, hphi, u6ehi7, u6elo5]
                      · linarith only [h2021, h2061, h2065, hlam]
                    · linarith only [h1622, h1790, h2021, h2061, h2062, h2064, hlam, hphi, u6ehi7, u6elo3]
                  · linarith only [h2021, h2061, h2062, h2063, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2074 | h2074
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h2075 | h2075
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h2076 | h2076
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2077 | h2077
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2078 | h2078
                          · linarith only [h1622, h1790, h1791, h2061, h2078, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h2078, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h1622, h1790, h2077, hlam, hphi, u6ehi7, u6elo5]
                      · linarith only [h1791, h2061, h2062, h2076, hlam]
                    · linarith only [h1622, h1790, h1791, h2061, h2075, hlam, hphi, u6ehi7, u6elo3]
                  · linarith only [h1791, h2061, h2074, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2085 | h2085
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2086 | h2086
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h2087 | h2087
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h2088 | h2088
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2089 | h2089
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2090 | h2090
                          · linarith only [h1791, h2090, hc12, hlam, hphi, ht01, u0ehi7]
                          · linarith only [h0, h1790, h2090, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h0, h1790, h2061, h2089, hlam, hphi, u6ehi7, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2094 | h2094
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2095 | h2095
                          · linarith only [h0, h1790, h1791, h2095, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h2095, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h2088, h2094, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi9, u6elo5]
                    · linarith only [h2086, h2087, hc35, hlam, hphi, ht56, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h2100 | h2100
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h2101 | h2101
                      · linarith only [h2085, h2086, h2101, hlam]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2103 | h2103
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2104 | h2104
                          · linarith only [h0, h1790, h1791, h2104, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h2104, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h0, h1790, h2021, h2085, h2086, h2103, hlam, hphi, u6ehi7, u6elo5]
                    · linarith only [h0, h1790, h2021, h2085, h2100, hlam, hphi, u6ehi7, u6elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2109 | h2109
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h2110 | h2110
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h2111 | h2111
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2112 | h2112
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2113 | h2113
                          · linarith only [h0, h1790, h1791, h2113, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h2113, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h2112, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi10, u6elo5]
                      · linarith only [h2085, h2109, h2111, hlam]
                    · linarith only [h0, h1790, h2061, h2109, h2110, hlam, hphi, u6ehi7, u6elo3]
                  · rcases m.htr 0 3 6 (by decide) (by decide) with h2119 | h2119
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h2120 | h2120
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2121 | h2121
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2122 | h2122
                          · linarith only [h0, h1790, h1791, h2122, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h2122, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h2109, h2119, h2121, hlam, hphi, u6ehi9, u6elo5]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h2126 | h2126
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h2127 | h2127
                          · linarith only [h0, h1790, h1791, h2127, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi7]
                          · linarith only [h0, h1790, h2127, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi7]
                        · linarith only [h2120, h2126, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi9, u6elo5]
                    · linarith only [h0, h1790, h1791, h2119, hlam, hphi, u6ehi7, u6elo3]
        · linarith only [h1790, hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi6, u6elo1]

end R2N4
