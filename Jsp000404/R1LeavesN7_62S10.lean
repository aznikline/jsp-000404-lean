import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3222000 in
set_option maxHeartbeats 3222000 in
theorem r1l7_22_13_15_M_LI_L_0_L_I_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h12, h15, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h0, h12, h14, h15, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                              · linarith only [h0, h12, h14, h18, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · rcases h2bigk with h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [hc12, hlam, hphi, p20_1, u2elo0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h13, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p20_1, u2elo0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  rcases p20_3 (m.d 0 2) (by simp) with h24 | h24
                                  · rcases p20_3 (m.d 1 2) (by simp) with h25 | h25
                                    · linarith only [h0, h25, hlam]
                                    · linarith only [h25, h9, hlam]
                                  · linarith only [h24, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  rcases p20_3 (m.d 0 2) (by simp) with h29 | h29
                                  · rcases p20_3 (m.d 1 2) (by simp) with h30 | h30
                                    · linarith only [h0, h30, hlam]
                                    · linarith only [h10, h30, hlam]
                                  · linarith only [h29, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h0, hlam, p20_1]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h13, h18, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo1]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  rcases p20_3 (m.d 0 2) (by simp) with h37 | h37
                                  · rcases p20_3 (m.d 1 2) (by simp) with h38 | h38
                                    · rcases p20_3 (m.d 2 3) (by simp) with h39 | h39
                                      · linarith only [h39, h8, hlam]
                                      · linarith only [h12, h39, hlam]
                                    · linarith only [h38, hlam, p20_0]
                                  · linarith only [h37, h4, hlam]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  rcases p20_3 (m.d 0 2) (by simp) with h44 | h44
                                  · rcases p20_3 (m.d 1 2) (by simp) with h45 | h45
                                    · rcases p20_3 (m.d 2 3) (by simp) with h46 | h46
                                      · linarith only [h46, h8, hlam]
                                      · linarith only [h13, h46, hlam]
                                    · linarith only [h45, hlam, p20_0]
                                  · linarith only [h44, h5, hlam]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h3, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h8, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h12, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h0, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p20_1, u2elo0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h4, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h9, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h12, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h14, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h5, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h10, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h13, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h12, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [hlam, p20_0]
                          · linarith only [h13, h6, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h69 | h69
                              · rcases h2bigk with h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [hlam, p70_0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [hc12, hlam, hphi, p70_1, u2elo0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h67, h69, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p70_1, u2elo0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h12, h67, h69, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p70_1, u2elo0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  rcases p70_3 (m.d 0 2) (by simp) with h75 | h75
                                  · rcases p70_3 (m.d 1 2) (by simp) with h76 | h76
                                    · linarith only [h0, h76, hlam]
                                    · linarith only [h10, h76, hlam]
                                  · linarith only [h75, hlam, p70_0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h0, hlam, p70_1]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [hlam, p70_0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h67, h69, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p70_1, u2elo1]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h0, h12, h67, h69, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p70_1, u2elo0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  rcases p70_3 (m.d 0 2) (by simp) with h84 | h84
                                  · rcases p70_3 (m.d 1 2) (by simp) with h85 | h85
                                    · rcases p70_3 (m.d 2 3) (by simp) with h86 | h86
                                      · linarith only [h8, h86, hlam]
                                      · linarith only [h67, h86, hlam]
                                    · linarith only [h85, hlam, p70_0]
                                  · linarith only [h5, h84, hlam]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h3, hlam, p70_0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h8, hlam, p70_0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [hlam, p70_0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h12, hlam, p70_1]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h12, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p70_1, u3elo3]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h4, hlam, p70_0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h9, hlam, p70_0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p70_1, u2elo0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [hlam, p70_0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h0, h67, h69, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p70_1, u2elo0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h5, hlam, p70_0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h10, hlam, p70_0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h67, hlam, p70_0]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [h68, hlam, p70_1]
                                · have p70_0 := h70c.1
                                  have p70_1 := h70c.2.1
                                  have p70_2 := h70c.2.2.1
                                  have p70_3 := h70c.2.2.2
                                  linarith only [hlam, p70_0]
                              · linarith only [h12, h4, h69, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · linarith only [h12, h4, h67, h68, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                          · linarith only [h6, h67, hc23, hlam, hphi, u3elo0]
                      · linarith only [h11, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h10, h5, hc12, hlam, hphi, u2elo0]
                  · linarith only [h4, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · linarith only [h3, h8, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
                · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                            · linarith only [h113, h117, h119, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                              · linarith only [h117, h121, h4, h7, hlam]
                              · rcases h2bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hc12, hlam, hphi, p123_1, u2elo0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h118, h121, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p123_1, u2elo0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 2) (by simp) with h127 | h127
                                  · rcases p123_3 (m.d 1 2) (by simp) with h128 | h128
                                    · linarith only [h0, h128, hlam]
                                    · linarith only [h114, h128, hlam]
                                  · linarith only [h127, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 2) (by simp) with h132 | h132
                                  · rcases p123_3 (m.d 1 2) (by simp) with h133 | h133
                                    · linarith only [h0, h133, hlam]
                                    · linarith only [h115, h133, hlam]
                                  · linarith only [h132, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h0, hlam, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h118, h121, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p123_1, u2elo1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 2) (by simp) with h140 | h140
                                  · rcases p123_3 (m.d 1 2) (by simp) with h141 | h141
                                    · rcases p123_3 (m.d 2 3) (by simp) with h142 | h142
                                      · linarith only [h113, h142, hlam]
                                      · linarith only [h117, h142, hlam]
                                    · linarith only [h141, hlam, p123_0]
                                  · linarith only [h140, h4, hlam]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 2) (by simp) with h147 | h147
                                  · rcases p123_3 (m.d 1 2) (by simp) with h148 | h148
                                    · rcases p123_3 (m.d 2 3) (by simp) with h149 | h149
                                      · linarith only [h113, h149, hlam]
                                      · linarith only [h118, h149, hlam]
                                    · linarith only [h148, hlam, p123_0]
                                  · linarith only [h147, h5, hlam]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h3, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h113, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h117, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p123_1, u2elo0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h0, h113, h117, h119, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p123_1, u2elo0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h4, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h114, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h117, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h119, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h5, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h115, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h118, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h117, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p123_1, u2elo0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                          · linarith only [h118, h6, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h170 | h170
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h171 | h171
                            · linarith only [h171, h4, h7, hlam]
                            · linarith only [h117, h170, h171, hlam]
                          · linarith only [h170, h6, hc23, hlam, hphi, u3elo0]
                      · linarith only [h116, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h115, h5, hc12, hlam, hphi, u2elo0]
                  · linarith only [h113, h114, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · linarith only [h113, h3, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h179 | h179
              · rcases m.htr 1 2 3 (by decide) (by decide) with h180 | h180
                · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
                      · linarith only [h183, h6, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h186 | h186
                          · linarith only [h1, h180, h186, h6, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h188 | h188
                            · linarith only [h185, h186, h188, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h190 | h190
                              · linarith only [h182, h185, h186, h188, h190, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h179, h190, h6, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h193 | h193
                          · linarith only [h1, h180, h193, h6, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h195 | h195
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h196 | h196
                              · rcases h2bigk with h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [hlam, p197_0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [hc12, hlam, hphi, p197_1, u2elo0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  rcases p197_3 (m.d 0 2) (by simp) with h200 | h200
                                  · rcases p197_3 (m.d 1 2) (by simp) with h201 | h201
                                    · linarith only [h0, h201, hlam]
                                    · linarith only [h180, h201, hlam]
                                  · linarith only [h200, hlam, p197_0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h195, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p197_1, u2elo0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  rcases p197_3 (m.d 0 2) (by simp) with h206 | h206
                                  · rcases p197_3 (m.d 1 2) (by simp) with h207 | h207
                                    · linarith only [h0, h207, hlam]
                                    · linarith only [h182, h207, hlam]
                                  · linarith only [h206, hlam, p197_0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h0, hlam, p197_1]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [hlam, p197_0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  rcases p197_3 (m.d 0 2) (by simp) with h213 | h213
                                  · rcases p197_3 (m.d 1 2) (by simp) with h214 | h214
                                    · rcases p197_3 (m.d 2 3) (by simp) with h215 | h215
                                      · linarith only [h215, hlam, p197_0]
                                      · rcases p197_3 (m.d 2 4) (by simp) with h217 | h217
                                        · linarith only [h181, h217, hlam]
                                        · linarith only [h185, h217, hlam]
                                    · linarith only [h214, hlam, p197_0]
                                  · linarith only [h213, h3, hlam]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h195, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p197_1, u2elo1]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  rcases p197_3 (m.d 0 2) (by simp) with h223 | h223
                                  · rcases p197_3 (m.d 1 2) (by simp) with h224 | h224
                                    · rcases p197_3 (m.d 2 3) (by simp) with h225 | h225
                                      · linarith only [h180, h225, hlam]
                                      · rcases p197_3 (m.d 2 4) (by simp) with h227 | h227
                                        · linarith only [h181, h227, hlam]
                                        · linarith only [h195, h227, hlam]
                                    · linarith only [h224, hlam, p197_0]
                                  · linarith only [h223, h5, hlam]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h3, hlam, p197_0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h180, hlam, p197_0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [hlam, p197_0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h185, hlam, p197_1]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h193, hlam, p197_1]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h4, hlam, p197_0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h181, hlam, p197_0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p197_1, u2elo0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [hlam, p197_0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h0, h181, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p197_1, u2elo0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h5, hlam, p197_0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h182, hlam, p197_0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p197_1, u2elo0]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [h195, hlam, p197_1]
                                · have p197_0 := h197c.1
                                  have p197_1 := h197c.2.1
                                  have p197_2 := h197c.2.2.1
                                  have p197_3 := h197c.2.2.2
                                  linarith only [hlam, p197_0]
                              · linarith only [h179, h185, h196, h6, hc23, hlam, hphi, u3elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h248 | h248
                              · linarith only [h185, h195, h248, hc23, hlam, hphi, u3elo3]
                              · linarith only [h179, h185, h248, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h182, h5, hc12, hlam, hphi, u2elo0]
                  · linarith only [h180, h181, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · linarith only [h180, h3, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
                · rcases m.htr 1 2 4 (by decide) (by decide) with h255 | h255
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h256 | h256
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h257 | h257
                      · linarith only [h1, h257, h6, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h259 | h259
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
                          · linarith only [h1, h254, h260, h6, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h262 | h262
                            · linarith only [h1, h179, h254, h259, h262, h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h264 | h264
                              · linarith only [h1, h179, h254, h259, h264, h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · rcases h2bigk with h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [hc12, hlam, hphi, p266_1, u2elo0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h259, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p266_1, u2elo0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  rcases p266_3 (m.d 0 2) (by simp) with h270 | h270
                                  · rcases p266_3 (m.d 1 2) (by simp) with h271 | h271
                                    · linarith only [h0, h271, hlam]
                                    · linarith only [h255, h271, hlam]
                                  · linarith only [h270, hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h259, h260, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p266_1, u2elo0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h0, hlam, p266_1]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h259, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p266_1, u2elo1]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  rcases p266_3 (m.d 0 2) (by simp) with h279 | h279
                                  · rcases p266_3 (m.d 1 2) (by simp) with h280 | h280
                                    · rcases p266_3 (m.d 2 3) (by simp) with h281 | h281
                                      · linarith only [h254, h281, hlam]
                                      · linarith only [h259, h281, hlam]
                                    · linarith only [h280, hlam, p266_0]
                                  · linarith only [h279, h4, hlam]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h0, h259, h260, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p266_1, u2elo0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h3, hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h254, hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h259, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p266_1, u2elo0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h260, hlam, p266_1]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h4, hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h255, hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h259, hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h262, hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h5, hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h256, hlam, p266_0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p266_1, u2elo0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [h0, h256, h259, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p266_1, u2elo0]
                                · have p266_0 := h266c.1
                                  have p266_1 := h266c.2.1
                                  have p266_2 := h266c.2.2.1
                                  have p266_3 := h266c.2.2.2
                                  linarith only [hlam, p266_0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h302 | h302
                          · linarith only [h259, h302, h6, hc03, hlam, hphi, u3elo3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h304 | h304
                            · linarith only [h179, h304, h4, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h306 | h306
                              · linarith only [h179, h259, h306, h4, hc23, hlam, hphi, u3elo3]
                              · rcases h2bigk with h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [hc12, hlam, hphi, p308_1, u2elo0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  rcases p308_3 (m.d 0 2) (by simp) with h311 | h311
                                  · rcases p308_3 (m.d 1 2) (by simp) with h312 | h312
                                    · linarith only [h0, h312, hlam]
                                    · linarith only [h254, h312, hlam]
                                  · linarith only [h311, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  rcases p308_3 (m.d 0 2) (by simp) with h316 | h316
                                  · rcases p308_3 (m.d 1 2) (by simp) with h317 | h317
                                    · linarith only [h0, h317, hlam]
                                    · linarith only [h255, h317, hlam]
                                  · linarith only [h316, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  rcases p308_3 (m.d 0 2) (by simp) with h321 | h321
                                  · rcases p308_3 (m.d 1 2) (by simp) with h322 | h322
                                    · linarith only [h0, h322, hlam]
                                    · linarith only [h256, h322, hlam]
                                  · linarith only [h321, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h0, hlam, p308_1]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  rcases p308_3 (m.d 0 2) (by simp) with h328 | h328
                                  · rcases p308_3 (m.d 1 2) (by simp) with h329 | h329
                                    · rcases p308_3 (m.d 2 3) (by simp) with h330 | h330
                                      · linarith only [h330, hlam, p308_0]
                                      · rcases p308_3 (m.d 2 4) (by simp) with h332 | h332
                                        · linarith only [h255, h332, hlam]
                                        · linarith only [h259, h332, hlam]
                                    · linarith only [h329, hlam, p308_0]
                                  · linarith only [h3, h328, hlam]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  rcases p308_3 (m.d 0 2) (by simp) with h337 | h337
                                  · rcases p308_3 (m.d 1 2) (by simp) with h338 | h338
                                    · rcases p308_3 (m.d 2 3) (by simp) with h339 | h339
                                      · linarith only [h254, h339, hlam]
                                      · rcases p308_3 (m.d 2 4) (by simp) with h341 | h341
                                        · linarith only [h341, hlam, p308_0]
                                        · rcases p308_3 (m.d 2 5) (by simp) with h343 | h343
                                          · linarith only [h256, h343, hlam]
                                          · linarith only [h304, h343, hlam]
                                    · linarith only [h338, hlam, p308_0]
                                  · linarith only [h337, h4, hlam]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  rcases p308_3 (m.d 0 2) (by simp) with h348 | h348
                                  · rcases p308_3 (m.d 1 2) (by simp) with h349 | h349
                                    · rcases p308_3 (m.d 2 3) (by simp) with h350 | h350
                                      · linarith only [h254, h350, hlam]
                                      · rcases p308_3 (m.d 2 4) (by simp) with h352 | h352
                                        · linarith only [h255, h352, hlam]
                                        · rcases p308_3 (m.d 2 5) (by simp) with h354 | h354
                                          · linarith only [h354, hlam, p308_0]
                                          · rcases h5bigk with h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [hlam, p356_0]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h256, h259, h304, h6, hc23, hlam, hphi, p356_1, u3elo4]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h259, h304, h6, hc23, hlam, hphi, p356_1, u3elo4]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h6, hlam, p356_0]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h179, hlam, p356_0]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h2, hlam, p356_0]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [hlam, p356_0]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h2, h259, h304, h6, hc23, hlam, hphi, p356_1, u3elo4]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h257, hlam, p356_0]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h2, h259, h306, h6, hc23, hlam, hphi, p356_1, u3elo4]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h5, hlam, p356_1]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h256, hlam, p356_1]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [hlam, p356_0]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h302, hlam, p356_1]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h304, hlam, p356_0]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h259, h304, h5, hc23, hlam, hphi, p356_1, u3elo4]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h256, h259, h304, hc23, hlam, hphi, p356_1, u3elo4]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h259, h304, hc23, hlam, hphi, p356_1, u3elo4]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [hlam, p356_0]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h306, hlam, p356_0]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              rcases p356_3 (m.d 0 5) (by simp) with h377 | h377
                                              · linarith only [h179, h377, hlam]
                                              · rcases p356_3 (m.d 1 5) (by simp) with h379 | h379
                                                · linarith only [h2, h379, hlam, p356_1]
                                                · rcases p356_3 (m.d 2 5) (by simp) with h381 | h381
                                                  · linarith only [h304, h381, hlam]
                                                  · rcases p356_3 (m.d 3 5) (by simp) with h383 | h383
                                                    · linarith only [h306, h383, hlam]
                                                    · linarith only [h383, h6, hlam]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              rcases p356_3 (m.d 0 5) (by simp) with h386 | h386
                                              · linarith only [h179, h386, hlam]
                                              · linarith only [h2, h386, hlam]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              rcases p356_3 (m.d 0 5) (by simp) with h389 | h389
                                              · linarith only [h179, h389, hlam]
                                              · linarith only [h389, h5, hlam]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [h1, h254, h6, hc23, hc45, hlam, hphi, ht34, p356_1]
                                            · have p356_0 := h356c.1
                                              have p356_1 := h356c.2.1
                                              have p356_2 := h356c.2.2.1
                                              have p356_3 := h356c.2.2.2
                                              linarith only [hlam, p356_0]
                                    · linarith only [h349, hlam, p308_0]
                                  · linarith only [h348, h5, hlam]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h3, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h254, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h259, hlam, p308_1]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h302, hlam, p308_1]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h4, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h255, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p308_1, u2elo0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h304, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h5, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h256, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h0, h256, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p308_1, u2elo0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h0, h256, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p308_1, u2elo0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [hlam, p308_0]
                    · linarith only [h256, h5, hc12, hlam, hphi, u2elo0]
                  · linarith only [h254, h255, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · linarith only [h254, h3, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h414 | h414
            · linarith only [h3, h414, h5, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h416 | h416
              · linarith only [h4, h416, h5, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h418 | h418
                · rcases m.htr 1 2 4 (by decide) (by decide) with h419 | h419
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h420 | h420
                    · linarith only [h0, h420, h5, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h422 | h422
                      · linarith only [h1, h414, h422, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h424 | h424
                        · linarith only [h0, h418, h424, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h426 | h426
                          · linarith only [h0, h414, h419, h424, h426, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                          · linarith only [h0, h419, h424, h426, h5, hc23, hlam, hphi, u3elo4]
                  · linarith only [h4, h419, h5, hc12, hlam, hphi, u2elo4]
                · linarith only [h3, h418, h5, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h431 | h431
          · rcases m.htr 0 3 5 (by decide) (by decide) with h432 | h432
            · rcases m.htr 0 4 5 (by decide) (by decide) with h433 | h433
              · rcases m.htr 1 2 3 (by decide) (by decide) with h434 | h434
                · rcases m.htr 1 2 4 (by decide) (by decide) with h435 | h435
                  · linarith only [h4, h435, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h437 | h437
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h438 | h438
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h439 | h439
                        · linarith only [h0, h4, h434, h439, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                        · linarith only [h0, h4, h434, h439, hc23, hlam, hphi, u3elo3]
                      · linarith only [h3, h4, h432, h438, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h4, h431, h437, hc12, hlam, hphi, u2elo3]
                · linarith only [h3, h4, h434, hc12, hlam, hphi, u2elo3]
              · linarith only [h3, h4, h432, h433, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h446 | h446
              · rcases m.htr 1 2 3 (by decide) (by decide) with h447 | h447
                · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
                  · linarith only [h0, h4, h448, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h450 | h450
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h451 | h451
                      · linarith only [h432, h451, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h453 | h453
                        · linarith only [h3, h4, h453, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                        · linarith only [h0, h4, h447, h453, hc23, hlam, hphi, u3elo3]
                    · linarith only [h4, h431, h447, h450, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h3, h4, h447, hc12, hlam, hphi, u2elo3]
              · linarith only [h4, h431, h446, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h459 | h459
            · linarith only [h3, h431, h459, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h461 | h461
              · rcases m.htr 1 2 3 (by decide) (by decide) with h462 | h462
                · rcases m.htr 1 2 4 (by decide) (by decide) with h463 | h463
                  · linarith only [h0, h4, h463, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h465 | h465
                    · linarith only [h0, h431, h465, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h467 | h467
                      · linarith only [h1, h459, h467, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h469 | h469
                        · linarith only [h0, h4, h462, h469, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                        · linarith only [h0, h4, h462, h469, hc23, hlam, hphi, u3elo3]
                · linarith only [h3, h4, h462, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h473 | h473
                · rcases m.htr 1 2 4 (by decide) (by decide) with h474 | h474
                  · linarith only [h0, h4, h474, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h476 | h476
                    · linarith only [h0, h431, h476, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h478 | h478
                      · linarith only [h1, h459, h478, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h480 | h480
                        · linarith only [h0, h4, h473, h480, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                        · linarith only [h0, h4, h473, h480, hc23, hlam, hphi, u3elo3]
                · linarith only [h3, h4, h473, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h484 | h484
        · rcases m.htr 0 2 5 (by decide) (by decide) with h485 | h485
          · rcases m.htr 0 3 5 (by decide) (by decide) with h486 | h486
            · rcases m.htr 0 4 5 (by decide) (by decide) with h487 | h487
              · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
                · linarith only [h3, h488, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h491 | h491
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h492 | h492
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h493 | h493
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h494 | h494
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h495 | h495
                            · linarith only [h0, h3, h490, h495, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · linarith only [h3, h484, h487, h493, h495, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h3, h494, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h3, h493, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h486, h492, hc13, hlam, hphi, u3elo0]
                    · linarith only [h3, h485, h490, h491, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h3, h484, h490, hc12, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
                · linarith only [h3, h503, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h505 | h505
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h506 | h506
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h507 | h507
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h508 | h508
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h509 | h509
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h510 | h510
                            · linarith only [h0, h3, h487, h505, h510, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h512 | h512
                              · linarith only [h3, h484, h487, h508, h512, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · rcases h2bigk with h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h3, hc12, hlam, hphi, ht23, p514_1, u3elo2]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h3, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h3, h508, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p514_1, u3elo2]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h3, h508, h510, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p514_1, u3elo2]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h0, hlam, p514_1]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h503, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h0, h3, h508, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p514_1, u3elo2]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h0, h3, h508, h510, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p514_1, u3elo2]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p514_1, u3elo2]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p514_1, u3elo2]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  rcases p514_3 (m.d 0 2) (by simp) with h528 | h528
                                  · linarith only [h3, h528, hlam]
                                  · linarith only [h484, h528, hlam]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  rcases p514_3 (m.d 0 2) (by simp) with h531 | h531
                                  · linarith only [h3, h531, hlam]
                                  · linarith only [h485, h531, hlam]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h484, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h505, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h508, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h510, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h485, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h506, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h509, hlam, p514_0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [h0, h506, h508, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p514_1, u2elo0]
                                · have p514_0 := h514c.1
                                  have p514_1 := h514c.2.1
                                  have p514_2 := h514c.2.2.1
                                  have p514_3 := h514c.2.2.2
                                  linarith only [hlam, p514_0]
                          · linarith only [h3, h509, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h0, h3, h505, h508, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h486, h507, hc13, hlam, hphi, u3elo0]
                    · linarith only [h3, h485, h505, h506, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h3, h484, h505, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h3, h485, h486, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h550 | h550
            · rcases m.htr 0 4 5 (by decide) (by decide) with h551 | h551
              · linarith only [h484, h485, h551, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h553 | h553
                · linarith only [h0, h3, h553, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h555 | h555
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h556 | h556
                    · linarith only [h0, h485, h556, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h558 | h558
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h559 | h559
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h560 | h560
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h561 | h561
                            · linarith only [h484, h485, h551, h560, h561, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h563 | h563
                              · linarith only [h485, h559, h561, h563, hc02, hlam, hphi, u2elo3]
                              · rcases h2bigk with h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h485, h555, h559, h560, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p565_1, u3elo2]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h3, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h485, h559, h560, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p565_1, u3elo2]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h485, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h0, hlam, p565_1]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h553, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h0, h485, h559, h560, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p565_1, u3elo2]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h556, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p565_1, u3elo2]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p565_1, u3elo2]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  rcases p565_3 (m.d 0 2) (by simp) with h579 | h579
                                  · linarith only [h3, h579, hlam]
                                  · linarith only [h484, h579, hlam]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h0, h485, h555, h559, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p565_1, u3elo2]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h484, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h555, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h559, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h561, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h0, h555, h559, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p565_1, u2elo4]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h555, h559, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p565_1, u2elo4]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h560, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  rcases p565_3 (m.d 0 2) (by simp) with h591 | h591
                                  · linarith only [h485, h591, hlam]
                                  · linarith only [h484, h591, hlam]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [hlam, p565_0]
                          · linarith only [h0, h3, h555, h559, h560, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h3, h559, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h550, h558, hc13, hlam, hphi, u3elo0]
                  · linarith only [h3, h484, h555, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h599 | h599
              · linarith only [h484, h485, h599, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h601 | h601
                · linarith only [h0, h3, h550, h601, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h603 | h603
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h604 | h604
                    · linarith only [h485, h604, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h606 | h606
                      · linarith only [h1, h550, h606, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h608 | h608
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h609 | h609
                          · linarith only [h0, h3, h550, h603, h608, h609, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · linarith only [h0, h3, h603, h608, h609, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h3, h608, hc02, hlam, hphi, ht23, u3elo3]
                  · linarith only [h3, h484, h603, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h614 | h614
          · rcases m.htr 0 3 5 (by decide) (by decide) with h615 | h615
            · rcases m.htr 0 4 5 (by decide) (by decide) with h616 | h616
              · rcases m.htr 1 2 3 (by decide) (by decide) with h617 | h617
                · linarith only [h3, h617, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h619 | h619
                  · linarith only [h0, h484, h619, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h621 | h621
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h622 | h622
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h623 | h623
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h624 | h624
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h625 | h625
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h626 | h626
                              · rcases h2bigk with h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [hlam, p627_0]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h484, h621, h623, h624, h626, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p627_1, u2elo2]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h3, hlam, p627_0]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h484, hlam, p627_0]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h484, h623, h624, h626, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p627_1, u3elo2]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h0, hlam, p627_1]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [hlam, p627_0]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h617, hlam, p627_0]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h619, hlam, p627_0]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h0, h484, h623, h624, h626, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p627_1, u3elo2]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p627_1, u3elo2]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p627_1, u3elo2]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [hlam, p627_0]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h484, h614, h624, h626, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p627_1, u3elo2]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  rcases p627_3 (m.d 0 2) (by simp) with h642 | h642
                                  · linarith only [h3, h642, hlam]
                                  · linarith only [h614, h642, hlam]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h0, h621, h624, h626, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p627_1, u2elo3]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h621, h624, h626, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p627_1, u2elo3]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h623, hlam, p627_0]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [hlam, p627_0]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  rcases p627_3 (m.d 0 2) (by simp) with h649 | h649
                                  · linarith only [h484, h649, hlam]
                                  · linarith only [h614, h649, hlam]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h614, hlam, p627_0]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h621, hlam, p627_0]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h624, hlam, p627_0]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [h625, hlam, p627_1]
                                · have p627_0 := h627c.1
                                  have p627_1 := h627c.2.1
                                  have p627_2 := h627c.2.2.1
                                  have p627_3 := h627c.2.2.2
                                  linarith only [hlam, p627_0]
                              · linarith only [h0, h484, h621, h623, h625, h626, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h484, h616, h625, hlam]
                          · linarith only [h484, h623, h624, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h3, h623, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h615, h622, hc13, hlam, hphi, u3elo0]
                    · linarith only [h3, h614, h621, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h484, h614, h616, hlam]
            · linarith only [h3, h614, h615, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h665 | h665
            · rcases m.htr 0 4 5 (by decide) (by decide) with h666 | h666
              · rcases m.htr 1 2 3 (by decide) (by decide) with h667 | h667
                · linarith only [h0, h3, h667, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h669 | h669
                  · linarith only [h0, h484, h669, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h671 | h671
                    · linarith only [h0, h614, h671, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h673 | h673
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h674 | h674
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h675 | h675
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h676 | h676
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h677 | h677
                              · rcases h2bigk with h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [hlam, p678_0]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h614, h674, h676, hc12, hlam, hphi, ht23, p678_1, u3elo2]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h3, hlam, p678_0]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h484, hlam, p678_0]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h614, hlam, p678_0]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h0, hlam, p678_1]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [hlam, p678_0]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h667, hlam, p678_0]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h669, hlam, p678_0]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h671, hlam, p678_0]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p678_1, u3elo2]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p678_1, u3elo2]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [hlam, p678_0]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h0, h484, hc12, hlam, hphi, ht23, p678_1, u3elo2]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h0, h614, hc12, hlam, hphi, ht23, p678_1, u3elo2]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p678_1, u2elo3]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [hc12, hlam, hphi, p678_1, u2elo3]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h674, hlam, p678_0]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [hlam, p678_0]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h0, h614, h674, hc12, hlam, hphi, ht23, p678_1, u3elo2]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p678_1, u2elo4]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [hc12, hlam, hphi, p678_1, u2elo4]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h675, hlam, p678_0]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [h676, hlam, p678_1]
                                · have p678_0 := h678c.1
                                  have p678_1 := h678c.2.1
                                  have p678_2 := h678c.2.2.1
                                  have p678_3 := h678c.2.2.2
                                  linarith only [hlam, p678_0]
                              · rcases h2bigk with h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hc12, hlam, hphi, p704_1, u2elo0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h3, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h484, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h614, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h0, hlam, p704_1]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h667, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h669, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h671, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p704_1, u3elo2]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p704_1, u3elo2]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h0, h484, hc12, hlam, hphi, ht23, p704_1, u3elo2]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h0, h614, hc12, hlam, hphi, ht23, p704_1, u3elo2]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p704_1, u2elo3]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hc12, hlam, hphi, p704_1, u2elo3]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h674, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h0, h614, h674, hc12, hlam, hphi, ht23, p704_1, u3elo2]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p704_1, u2elo4]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hc12, hlam, hphi, p704_1, u2elo4]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h675, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h676, hlam, p704_1]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hlam, p704_0]
                            · linarith only [h0, h484, h665, h666, h676, hc12, hlam, hphi, ht23, u3elo0]
                          · linarith only [h0, h3, h675, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h0, h3, h674, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h665, h673, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h734 | h734
                · linarith only [h0, h3, h734, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h736 | h736
                  · linarith only [h0, h484, h736, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h738 | h738
                    · linarith only [h0, h614, h738, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h740 | h740
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h741 | h741
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h742 | h742
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h743 | h743
                            · linarith only [h484, h666, h741, h743, hc02, hlam, hphi, ht23, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h745 | h745
                              · linarith only [h741, h743, h745, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                              · rcases h2bigk with h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h484, hc12, hlam, hphi, p747_1, u2elo3]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h3, hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h484, hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h614, hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h0, hlam, p747_1]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h734, hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h736, hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h738, hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p747_1, u3elo2]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p747_1, u3elo2]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h0, h484, hc12, hlam, hphi, ht23, p747_1, u3elo2]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h0, h614, hc12, hlam, hphi, ht23, p747_1, u3elo2]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p747_1, u2elo3]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [hc12, hlam, hphi, p747_1, u2elo3]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h741, hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h743, hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p747_1, u2elo4]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [hc12, hlam, hphi, p747_1, u2elo4]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h742, hlam, p747_0]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [h0, h484, h742, hc12, hlam, hphi, ht23, p747_1, u3elo2]
                                · have p747_0 := h747c.1
                                  have p747_1 := h747c.2.1
                                  have p747_2 := h747c.2.2.1
                                  have p747_3 := h747c.2.2.2
                                  linarith only [hlam, p747_0]
                          · linarith only [h1, h740, h742, hc23, hlam, hphi, u3elo0]
                        · linarith only [h0, h3, h741, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h665, h740, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h776 | h776
              · rcases m.htr 1 2 3 (by decide) (by decide) with h777 | h777
                · linarith only [h0, h3, h777, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h779 | h779
                  · linarith only [h0, h484, h779, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h781 | h781
                    · linarith only [h0, h614, h781, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h783 | h783
                      · linarith only [h3, h665, h783, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h785 | h785
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h786 | h786
                          · linarith only [h0, h3, h665, h786, hc12, hlam, hphi, u2elo2]
                          · linarith only [h0, h3, h786, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h0, h3, h785, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h790 | h790
                · linarith only [h0, h3, h790, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h792 | h792
                  · linarith only [h0, h484, h792, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h794 | h794
                    · linarith only [h0, h614, h794, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h796 | h796
                      · linarith only [h1, h665, h796, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h798 | h798
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h799 | h799
                          · linarith only [h1, h665, h799, hc13, hlam, hphi, u3elo2]
                          · linarith only [h0, h3, h799, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h0, h3, h798, hc12, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h803 | h803
      · rcases m.htr 0 2 4 (by decide) (by decide) with h804 | h804
        · rcases m.htr 0 2 5 (by decide) (by decide) with h805 | h805
          · linarith only [h0, h2, h805, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h807 | h807
            · linarith only [h1, h2, h807, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h809 | h809
              · linarith only [h0, h2, h804, h809, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h811 | h811
                · linarith only [h0, h2, h807, h811, hc23, hlam, hphi, u3elo4]
                · linarith only [h803, h805, h811, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h814 | h814
          · linarith only [h0, h2, h804, h814, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h816 | h816
            · linarith only [h1, h2, h816, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h818 | h818
              · rcases m.htr 1 2 3 (by decide) (by decide) with h819 | h819
                · linarith only [h0, h2, h816, h819, hc23, hlam, hphi, u3elo4]
                · linarith only [h803, h804, h819, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h822 | h822
                · linarith only [h0, h2, h816, h822, hc23, hlam, hphi, u3elo4]
                · linarith only [h803, h804, h822, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h825 | h825
        · rcases m.htr 0 2 5 (by decide) (by decide) with h826 | h826
          · linarith only [h0, h2, h803, h826, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h828 | h828
            · linarith only [h1, h2, h828, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h830 | h830
              · linarith only [h0, h2, h803, h825, h828, h830, hc12, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h832 | h832
                · linarith only [h0, h803, h828, h832, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h834 | h834
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h835 | h835
                    · linarith only [h0, h2, h803, h826, h835, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h1, h2, h832, h834, h835, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · linarith only [h803, h825, h828, h834, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h839 | h839
          · linarith only [h0, h2, h825, h839, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h841 | h841
            · linarith only [h1, h2, h841, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h843 | h843
              · rcases m.htr 1 2 3 (by decide) (by decide) with h844 | h844
                · linarith only [h0, h803, h841, h844, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h846 | h846
                  · linarith only [h0, h825, h846, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h848 | h848
                    · linarith only [h1, h2, h839, h844, h848, hlam]
                    · linarith only [h1, h2, h844, h848, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h851 | h851
                · linarith only [h0, h803, h851, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h853 | h853
                  · linarith only [h0, h825, h853, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h855 | h855
                    · linarith only [h0, h839, h855, hlam]
                    · linarith only [h0, h2, h855, hc12, hlam, hphi, u2elo4]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
