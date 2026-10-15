import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h12, h15, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h12, h14, h15, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h10, h11, h14, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                            · linarith only [h12, h13, h19, hlam]
                            · linarith only [h0, h10, h11, h19, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h10, h12, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                            · linarith only [h0, h11, h23, h25, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                              · linarith only [h0, h11, h23, h27, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases h2bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, h24, h27, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p29_1]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  rcases p29_3 (m.d 0 2) (by simp) with h32 | h32
                                  · rcases p29_3 (m.d 1 2) (by simp) with h33 | h33
                                    · linarith only [h0, h33, hlam]
                                    · linarith only [h33, h7, hlam]
                                  · linarith only [h32, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  rcases p29_3 (m.d 0 2) (by simp) with h37 | h37
                                  · rcases p29_3 (m.d 1 2) (by simp) with h38 | h38
                                    · linarith only [h0, h38, hlam]
                                    · linarith only [h38, h8, hlam]
                                  · linarith only [h37, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  rcases p29_3 (m.d 0 2) (by simp) with h42 | h42
                                  · rcases p29_3 (m.d 1 2) (by simp) with h43 | h43
                                    · linarith only [h0, h43, hlam]
                                    · linarith only [h43, h9, hlam]
                                  · linarith only [h42, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, h24, h25, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, h25, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h2, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h7, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hc23, hlam, hphi, p29_1, u2ehi3]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, h25, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h3, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h8, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h23, hlam, p29_1]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h25, hlam, p29_1]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h4, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h9, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h24, hlam, p29_1]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hc25, hlam, hphi, p29_1, u2ehi3]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h67 | h67
                            · linarith only [h11, h67, h8, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h69 | h69
                              · linarith only [h11, h69, h8, hc34, hlam, hphi, ht23, u2ehi3]
                              · rcases h2bigk with h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi4]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  rcases p71_3 (m.d 0 2) (by simp) with h74 | h74
                                  · rcases p71_3 (m.d 1 2) (by simp) with h75 | h75
                                    · linarith only [h0, h75, hlam]
                                    · linarith only [h7, h75, hlam]
                                  · linarith only [h74, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  rcases p71_3 (m.d 0 2) (by simp) with h79 | h79
                                  · rcases p71_3 (m.d 1 2) (by simp) with h80 | h80
                                    · linarith only [h0, h80, hlam]
                                    · linarith only [h8, h80, hlam]
                                  · linarith only [h79, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  rcases p71_3 (m.d 0 2) (by simp) with h84 | h84
                                  · rcases p71_3 (m.d 1 2) (by simp) with h85 | h85
                                    · linarith only [h0, h85, hlam]
                                    · linarith only [h85, h9, hlam]
                                  · linarith only [h84, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h0, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h0, h23, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p71_1]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi3]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h0, h24, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi2]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h2, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h7, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hc23, hlam, hphi, p71_1, u2ehi3]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h24, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h3, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h8, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h23, hlam, p71_1]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h67, hlam, p71_1]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h4, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h9, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hc25, hlam, hphi, p71_1, u2ehi2]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi3]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hlam, p71_0]
                        · linarith only [h0, h10, h23, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                        · linarith only [h10, h111, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h115 | h115
                              · rcases h2bigk with h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h0, h113, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p116_1, u2ehi4]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  rcases p116_3 (m.d 0 2) (by simp) with h119 | h119
                                  · rcases p116_3 (m.d 1 2) (by simp) with h120 | h120
                                    · linarith only [h0, h120, hlam]
                                    · linarith only [h120, h7, hlam]
                                  · linarith only [h119, hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  rcases p116_3 (m.d 0 2) (by simp) with h124 | h124
                                  · rcases p116_3 (m.d 1 2) (by simp) with h125 | h125
                                    · linarith only [h0, h125, hlam]
                                    · linarith only [h125, h8, hlam]
                                  · linarith only [h124, hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  rcases p116_3 (m.d 0 2) (by simp) with h129 | h129
                                  · rcases p116_3 (m.d 1 2) (by simp) with h130 | h130
                                    · linarith only [h0, h130, hlam]
                                    · linarith only [h130, h9, hlam]
                                  · linarith only [h129, hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h0, hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h0, h113, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p116_1, u2ehi4]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h0, h111, h113, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p116_1, u2ehi4]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p116_1, u2ehi4]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h2, hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h7, hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h111, hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [hc23, hlam, hphi, p116_1, u2ehi4]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h3, hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h8, hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [hc24, hlam, hphi, p116_1, u2ehi2]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [hc24, hlam, hphi, p116_1, u2ehi4]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h4, hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h9, hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h113, hlam, p116_1]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [h114, hlam, p116_0]
                                · have p116_0 := h116c.1
                                  have p116_1 := h116c.2.1
                                  have p116_2 := h116c.2.2.1
                                  have p116_3 := h116c.2.2.2
                                  linarith only [hlam, p116_0]
                              · linarith only [h0, h10, h113, h115, h2, h5, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                            · linarith only [h1, h110, h114, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h156 | h156
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h157 | h157
                              · rcases h2bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p158_1, u2ehi2]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  rcases p158_3 (m.d 0 2) (by simp) with h161 | h161
                                  · rcases p158_3 (m.d 1 2) (by simp) with h162 | h162
                                    · linarith only [h0, h162, hlam]
                                    · linarith only [h162, h7, hlam]
                                  · linarith only [h161, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  rcases p158_3 (m.d 0 2) (by simp) with h166 | h166
                                  · rcases p158_3 (m.d 1 2) (by simp) with h167 | h167
                                    · linarith only [h0, h167, hlam]
                                    · linarith only [h167, h8, hlam]
                                  · linarith only [h166, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  rcases p158_3 (m.d 0 2) (by simp) with h171 | h171
                                  · rcases p158_3 (m.d 1 2) (by simp) with h172 | h172
                                    · linarith only [h0, h172, hlam]
                                    · linarith only [h172, h9, hlam]
                                  · linarith only [h171, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h0, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p158_1, u2ehi2]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h0, h113, h156, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p158_1, u2ehi2]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h0, h113, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p158_1, u2ehi2]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h2, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h7, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h111, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h113, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h3, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h8, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hc24, hlam, hphi, p158_1, u2ehi2]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h0, h113, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p158_1, u2ehi2]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h4, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h9, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hc25, hlam, hphi, p158_1, u2ehi2]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h156, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hlam, p158_0]
                              · linarith only [h0, h10, h157, h2, h5, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h1, h110, h156, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                        · linarith only [h10, h198, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h200 | h200
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h201 | h201
                            · linarith only [h0, h110, h201, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h198, h200, h201, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                            · linarith only [h10, h110, h204, h7, hc24, hlam, hphi, u2ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h206 | h206
                              · linarith only [h10, h110, h206, h7, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h10, h206, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h7, h8, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
                · linarith only [h211, h7, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
                  · linarith only [h0, h2, h213, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h216 | h216
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h217 | h217
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h218 | h218
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h219 | h219
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h220 | h220
                              · rcases h2bigk with h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  rcases p221_3 (m.d 0 2) (by simp) with h223 | h223
                                  · rcases p221_3 (m.d 1 2) (by simp) with h224 | h224
                                    · linarith only [h0, h224, hlam]
                                    · rcases p221_3 (m.d 2 3) (by simp) with h226 | h226
                                      · linarith only [h2, h226, hlam]
                                      · linarith only [h226, h7, hlam]
                                  · linarith only [h0, h223, hlam]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h0, h213, h217, h219, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1, u2ehi1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h0, h213, h219, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1, u2ehi1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h0, h213, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1, u2ehi1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h0, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h7, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h211, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h213, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h2, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hc23, hlam, hphi, p221_1, u2ehi1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h0, h2, h213, h219, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1, u2ehi1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h0, h2, h213, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1, u2ehi1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h3, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hc24, hlam, hphi, p221_1, u2ehi1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h217, hlam, p221_1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h0, h2, h213, h217, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1, u2ehi1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h4, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hc25, hlam, hphi, p221_1, u2ehi1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h218, hlam, p221_1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h219, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hlam, p221_0]
                              · rcases h2bigk with h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [hlam, p253_0]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  rcases p253_3 (m.d 0 2) (by simp) with h255 | h255
                                  · rcases p253_3 (m.d 1 2) (by simp) with h256 | h256
                                    · linarith only [h0, h256, hlam]
                                    · rcases p253_3 (m.d 2 3) (by simp) with h258 | h258
                                      · linarith only [h2, h258, hlam]
                                      · linarith only [h258, h7, hlam]
                                  · linarith only [h0, h255, hlam]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h0, h211, h216, h217, h220, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p253_1]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h0, h211, h216, h220, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p253_1]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h0, h213, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi1]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h0, hlam, p253_0]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [hlam, p253_0]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h7, hlam, p253_0]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h211, hlam, p253_0]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h213, hlam, p253_0]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h2, hlam, p253_0]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [hc23, hlam, hphi, p253_1, u2ehi1]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [hlam, p253_0]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h0, h2, h211, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi1]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h0, h2, h213, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi1]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h3, hlam, p253_0]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [hc24, hlam, hphi, p253_1, u2ehi1]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h217, hlam, p253_1]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [hlam, p253_0]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h0, h2, h213, h217, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi1]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h4, hlam, p253_0]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [hc25, hlam, hphi, p253_1, u2ehi1]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h218, hlam, p253_1]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [h219, hlam, p253_0]
                                · have p253_0 := h253c.1
                                  have p253_1 := h253c.2.1
                                  have p253_2 := h253c.2.2.1
                                  have p253_3 := h253c.2.2.2
                                  linarith only [hlam, p253_0]
                            · linarith only [h1, h216, h219, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h218, h7, hc35, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h217, h7, hc34, hlam, hphi, ht23, u2ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h288 | h288
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h289 | h289
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h290 | h290
                            · linarith only [h211, h216, h288, h290, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h211, h290, h5, h6, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · linarith only [h289, h7, hc35, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h215, h288, h7, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h295 | h295
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h296 | h296
                        · linarith only [h215, h296, h7, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h2, h296, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h299 | h299
                        · linarith only [h215, h299, h7, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h2, h299, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
              · rcases m.htr 1 2 4 (by decide) (by decide) with h303 | h303
                · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h305 | h305
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h306 | h306
                      · linarith only [h1, h306, h6, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h308 | h308
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h310 | h310
                            · linarith only [h1, h303, h310, h6, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h312 | h312
                              · linarith only [h1, h302, h303, h308, h312, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases h2bigk with h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h0, h302, h309, h312, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p314_1]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  rcases p314_3 (m.d 0 2) (by simp) with h317 | h317
                                  · rcases p314_3 (m.d 1 2) (by simp) with h318 | h318
                                    · linarith only [h0, h318, hlam]
                                    · linarith only [h302, h318, hlam]
                                  · linarith only [h317, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  rcases p314_3 (m.d 0 2) (by simp) with h322 | h322
                                  · rcases p314_3 (m.d 1 2) (by simp) with h323 | h323
                                    · linarith only [h0, h323, hlam]
                                    · linarith only [h303, h323, hlam]
                                  · linarith only [h322, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  rcases p314_3 (m.d 0 2) (by simp) with h327 | h327
                                  · rcases p314_3 (m.d 1 2) (by simp) with h328 | h328
                                    · linarith only [h0, h328, hlam]
                                    · linarith only [h304, h328, hlam]
                                  · linarith only [h327, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h0, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h0, h309, h310, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p314_1, u2ehi3]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p314_1, u2ehi3]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h0, h310, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p314_1, u2ehi3]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h2, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h302, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hc23, hlam, hphi, p314_1, u2ehi3]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h0, h302, h310, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p314_1, u2ehi3]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h3, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h303, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h308, hlam, p314_1]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h310, hlam, p314_1]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h4, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h304, hlam, p314_0]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [h309, hlam, p314_1]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hc25, hlam, hphi, p314_1, u2ehi3]
                                · have p314_0 := h314c.1
                                  have p314_1 := h314c.2.1
                                  have p314_2 := h314c.2.2.1
                                  have p314_3 := h314c.2.2.2
                                  linarith only [hlam, p314_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h352 | h352
                            · linarith only [h1, h303, h352, h6, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h354 | h354
                              · linarith only [h1, h303, h354, h6, hc34, hlam, hphi, ht23, u2ehi3]
                              · rcases h2bigk with h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h0, h304, h308, h309, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p356_1]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  rcases p356_3 (m.d 0 2) (by simp) with h359 | h359
                                  · rcases p356_3 (m.d 1 2) (by simp) with h360 | h360
                                    · linarith only [h0, h360, hlam]
                                    · linarith only [h302, h360, hlam]
                                  · linarith only [h359, hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  rcases p356_3 (m.d 0 2) (by simp) with h364 | h364
                                  · rcases p356_3 (m.d 1 2) (by simp) with h365 | h365
                                    · linarith only [h0, h365, hlam]
                                    · linarith only [h303, h365, hlam]
                                  · linarith only [h364, hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  rcases p356_3 (m.d 0 2) (by simp) with h369 | h369
                                  · rcases p356_3 (m.d 1 2) (by simp) with h370 | h370
                                    · linarith only [h0, h370, hlam]
                                    · linarith only [h304, h370, hlam]
                                  · linarith only [h369, hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h0, hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h0, h308, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p356_1, u2ehi3]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p356_1, u2ehi3]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h0, h308, h309, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p356_1, u2ehi3]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h2, hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h302, hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [hc23, hlam, hphi, p356_1, u2ehi3]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h309, hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h3, hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h303, hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h308, hlam, p356_1]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h352, hlam, p356_1]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h4, hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h304, hlam, p356_0]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [hc25, hlam, hphi, p356_1, u2ehi2]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [h0, h304, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p356_1, u2ehi3]
                                · have p356_0 := h356c.1
                                  have p356_1 := h356c.2.1
                                  have p356_2 := h356c.2.2.1
                                  have p356_3 := h356c.2.2.2
                                  linarith only [hlam, p356_0]
                        · linarith only [h308, h5, h6, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h302, h305, h5, h6, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h302, h304, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h302, h303, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h398 | h398
                · linarith only [h302, h398, hc23, hlam, hphi, u2ehi3]
                · linarith only [h3, h398, h6, hc45, hlam, hphi, ht23, ht34, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h401 | h401
            · rcases m.htr 1 2 3 (by decide) (by decide) with h402 | h402
              · rcases m.htr 1 2 4 (by decide) (by decide) with h403 | h403
                · rcases m.htr 1 2 5 (by decide) (by decide) with h404 | h404
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h405 | h405
                    · linarith only [h0, h2, h402, h405, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h407 | h407
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
                        · linarith only [h2, h408, h5, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h410 | h410
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h411 | h411
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h412 | h412
                              · rcases h2bigk with h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h0, h402, h410, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p413_1, u2ehi4]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  rcases p413_3 (m.d 0 2) (by simp) with h416 | h416
                                  · rcases p413_3 (m.d 1 2) (by simp) with h417 | h417
                                    · linarith only [h0, h417, hlam]
                                    · linarith only [h402, h417, hlam]
                                  · linarith only [h416, hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  rcases p413_3 (m.d 0 2) (by simp) with h421 | h421
                                  · rcases p413_3 (m.d 1 2) (by simp) with h422 | h422
                                    · linarith only [h0, h422, hlam]
                                    · linarith only [h403, h422, hlam]
                                  · linarith only [h421, hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  rcases p413_3 (m.d 0 2) (by simp) with h426 | h426
                                  · rcases p413_3 (m.d 1 2) (by simp) with h427 | h427
                                    · linarith only [h0, h427, hlam]
                                    · linarith only [h404, h427, hlam]
                                  · linarith only [h426, hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h0, hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h0, h410, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p413_1, u2ehi4]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h0, h408, h410, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p413_1, u2ehi4]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p413_1, u2ehi4]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h2, hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h402, hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h408, hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [hc23, hlam, hphi, p413_1, u2ehi4]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h3, hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h403, hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [hc24, hlam, hphi, p413_1, u2ehi2]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [hc24, hlam, hphi, p413_1, u2ehi4]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h4, hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h404, hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h410, hlam, p413_1]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [h411, hlam, p413_0]
                                · have p413_0 := h413c.1
                                  have p413_1 := h413c.2.1
                                  have p413_2 := h413c.2.2.1
                                  have p413_3 := h413c.2.2.2
                                  linarith only [hlam, p413_0]
                              · linarith only [h2, h410, h412, h5, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                            · linarith only [h1, h407, h411, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h453 | h453
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h454 | h454
                              · rcases h2bigk with h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h0, h402, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p455_1, u2ehi2]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  rcases p455_3 (m.d 0 2) (by simp) with h458 | h458
                                  · rcases p455_3 (m.d 1 2) (by simp) with h459 | h459
                                    · linarith only [h0, h459, hlam]
                                    · linarith only [h402, h459, hlam]
                                  · linarith only [h458, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  rcases p455_3 (m.d 0 2) (by simp) with h463 | h463
                                  · rcases p455_3 (m.d 1 2) (by simp) with h464 | h464
                                    · linarith only [h0, h464, hlam]
                                    · linarith only [h403, h464, hlam]
                                  · linarith only [h463, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  rcases p455_3 (m.d 0 2) (by simp) with h468 | h468
                                  · rcases p455_3 (m.d 1 2) (by simp) with h469 | h469
                                    · linarith only [h0, h469, hlam]
                                    · linarith only [h404, h469, hlam]
                                  · linarith only [h468, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h0, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p455_1, u2ehi2]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h0, h410, h453, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p455_1, u2ehi2]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h0, h410, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p455_1, u2ehi2]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h2, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h402, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h408, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h410, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h3, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h403, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hc24, hlam, hphi, p455_1, u2ehi2]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h0, h403, h410, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p455_1, u2ehi2]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h4, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h404, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hc25, hlam, hphi, p455_1, u2ehi2]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h453, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hlam, p455_0]
                              · linarith only [h2, h454, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h1, h407, h453, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h401, h403, h407, h5, hc34, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h0, h4, h402, h404, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h402, h403, hc24, hlam, hphi, u2ehi2]
              · linarith only [h2, h402, h5, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h499 | h499
              · rcases m.htr 1 2 4 (by decide) (by decide) with h500 | h500
                · rcases m.htr 1 2 5 (by decide) (by decide) with h501 | h501
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h502 | h502
                    · linarith only [h0, h2, h499, h5, h502, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h504 | h504
                      · linarith only [h1, h401, h504, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h506 | h506
                        · linarith only [h2, h5, h506, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h508 | h508
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h509 | h509
                            · linarith only [h1, h401, h500, h509, hlam]
                            · linarith only [h506, h508, h509, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h512 | h512
                            · linarith only [h3, h401, h512, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h514 | h514
                              · linarith only [h1, h401, h499, h502, h514, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h2, h5, h514, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h4, h499, h501, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h499, h500, hc24, hlam, hphi, u2ehi2]
              · linarith only [h2, h499, h5, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h2, h4, hc25, hlam, hphi, u2ehi2]
      · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h522 | h522
      · linarith only [h2, h522, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h524 | h524
        · linarith only [h2, h524, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h526 | h526
          · rcases m.htr 0 4 5 (by decide) (by decide) with h527 | h527
            · rcases m.htr 1 2 3 (by decide) (by decide) with h528 | h528
              · linarith only [h0, h2, h528, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h530 | h530
                · linarith only [h0, h2, h530, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h532 | h532
                  · linarith only [h0, h524, h532, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h534 | h534
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h535 | h535
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h536 | h536
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h537 | h537
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h538 | h538
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h539 | h539
                              · rcases h2bigk with h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [hlam, p540_0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h524, h536, h538, hc23, hlam, hphi, p540_1, u2ehi1]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h2, hlam, p540_0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h522, hlam, p540_0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h524, hlam, p540_0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h0, hlam, p540_0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [hlam, p540_0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h528, hlam, p540_0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h530, hlam, p540_0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h532, hlam, p540_0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [hc23, hlam, hphi, p540_1, u2ehi0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [hc23, hlam, hphi, p540_1, u2ehi1]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [hlam, p540_0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [hc23, hlam, hphi, p540_1, u2ehi3]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h0, h524, hc23, hlam, hphi, p540_1, u2ehi1]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h0, hc24, hlam, hphi, p540_1, u2ehi1]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [hc24, hlam, hphi, p540_1, u2ehi1]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h536, hlam, p540_1]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [hlam, p540_0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h0, h524, h536, hc23, hlam, hphi, p540_1, u2ehi1]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h0, hc25, hlam, hphi, p540_1, u2ehi1]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [hc25, hlam, hphi, p540_1, u2ehi1]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h537, hlam, p540_1]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [h538, hlam, p540_0]
                                · have p540_0 := h540c.1
                                  have p540_1 := h540c.2.1
                                  have p540_2 := h540c.2.2.1
                                  have p540_3 := h540c.2.2.2
                                  linarith only [hlam, p540_0]
                              · rcases h2bigk with h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [hlam, p566_0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h2, hc23, hlam, hphi, p566_1, u2ehi1]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h2, hlam, p566_0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h522, hlam, p566_0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h524, hlam, p566_0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h0, hlam, p566_0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [hlam, p566_0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h528, hlam, p566_0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h530, hlam, p566_0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h532, hlam, p566_0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [hc23, hlam, hphi, p566_1, u2ehi0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [hc23, hlam, hphi, p566_1, u2ehi1]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [hlam, p566_0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [hc23, hlam, hphi, p566_1, u2ehi3]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h0, h524, hc23, hlam, hphi, p566_1, u2ehi1]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h0, hc24, hlam, hphi, p566_1, u2ehi1]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [hc24, hlam, hphi, p566_1, u2ehi1]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h536, hlam, p566_1]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [hlam, p566_0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h0, h524, h536, hc23, hlam, hphi, p566_1, u2ehi1]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h0, hc25, hlam, hphi, p566_1, u2ehi1]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [hc25, hlam, hphi, p566_1, u2ehi1]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h537, hlam, p566_1]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [h538, hlam, p566_0]
                                · have p566_0 := h566c.1
                                  have p566_1 := h566c.2.1
                                  have p566_2 := h566c.2.2.1
                                  have p566_3 := h566c.2.2.2
                                  linarith only [hlam, p566_0]
                            · linarith only [h0, h522, h538, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                          · linarith only [h0, h2, h537, hc35, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h0, h2, h536, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h522, h527, h530, h535, hc24, hlam, hphi, u2ehi1]
                    · linarith only [h2, h526, h528, h534, hc23, hlam, hphi, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h597 | h597
              · linarith only [h0, h2, h597, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h599 | h599
                · linarith only [h0, h522, h527, h599, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h601 | h601
                  · linarith only [h0, h522, h527, h601, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h603 | h603
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h604 | h604
                      · linarith only [h1, h522, h527, h604, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h606 | h606
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h607 | h607
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h608 | h608
                            · linarith only [h0, h522, h527, h608, hc24, hlam, hphi, u2ehi1]
                            · linarith only [h0, h522, h608, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                          · linarith only [h0, h2, h607, hc35, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h0, h2, h606, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h2, h526, h597, h603, hc23, hlam, hphi, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h614 | h614
            · rcases m.htr 1 2 3 (by decide) (by decide) with h615 | h615
              · linarith only [h0, h2, h615, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h617 | h617
                · linarith only [h0, h2, h526, h617, hc34, hlam, hphi, ht23, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h619 | h619
                  · linarith only [h0, h2, h526, h619, hc34, hlam, hphi, ht23, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h621 | h621
                    · linarith only [h2, h526, h615, h621, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h623 | h623
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h624 | h624
                        · linarith only [h0, h2, h526, h624, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h2, h624, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h522, h614, h615, h621, h623, hc24, hlam, hphi, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h628 | h628
              · linarith only [h0, h2, h628, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h630 | h630
                · linarith only [h0, h522, h630, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h632 | h632
                  · linarith only [h0, h524, h632, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h634 | h634
                    · linarith only [h0, h2, h526, h628, h634, hc23, hlam, hphi, u2ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h636 | h636
                      · linarith only [h1, h614, h636, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h638 | h638
                        · linarith only [h0, h2, h526, h638, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h2, h638, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h641 | h641
    · rcases m.htr 0 2 4 (by decide) (by decide) with h642 | h642
      · linarith only [h0, h1, h642, hlam]
      · linarith only [h641, h642, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h645 | h645
      · linarith only [h641, h645, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h647 | h647
        · linarith only [h641, h647, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h649 | h649
          · rcases m.htr 0 4 5 (by decide) (by decide) with h650 | h650
            · rcases m.htr 1 2 3 (by decide) (by decide) with h651 | h651
              · linarith only [h0, h1, h641, h649, h651, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h653 | h653
                · linarith only [h0, h647, h653, hc25, hlam, hphi, u2ehi3]
                · linarith only [h0, h1, h653, hc24, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h650, hc45, hlam, hphi, ht23, ht34, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h657 | h657
            · rcases m.htr 1 2 3 (by decide) (by decide) with h658 | h658
              · linarith only [h0, h1, h658, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h660 | h660
                · linarith only [h0, h1, h660, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h0, h1, h660, hc24, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h657, hc45, hlam, hphi, ht23, ht34, u2ehi1]

end R2N4
