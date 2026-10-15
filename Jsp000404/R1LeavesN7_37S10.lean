import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
  · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
    · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
      · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
        · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h0, h14, h17, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · linarith only [h0, h14, h16, h17, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                      · linarith only [h16, h20, h4, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases h2bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hc12, hlam, hphi, p22_1, u2elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h15, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p22_1, u2elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          rcases p22_3 (m.d 0 2) (by simp) with h26 | h26
                          · rcases p22_3 (m.d 1 2) (by simp) with h27 | h27
                            · linarith only [h0, h27, hlam]
                            · linarith only [h27, h9, hlam]
                          · linarith only [h26, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          rcases p22_3 (m.d 0 2) (by simp) with h31 | h31
                          · rcases p22_3 (m.d 1 2) (by simp) with h32 | h32
                            · linarith only [h0, h32, hlam]
                            · linarith only [h10, h32, hlam]
                          · linarith only [h31, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h15, h20, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22_1, u2elo1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          rcases p22_3 (m.d 0 2) (by simp) with h39 | h39
                          · rcases p22_3 (m.d 1 2) (by simp) with h40 | h40
                            · rcases p22_3 (m.d 2 3) (by simp) with h41 | h41
                              · linarith only [h41, h8, hlam]
                              · linarith only [h14, h41, hlam]
                            · linarith only [h40, hlam, p22_0]
                          · linarith only [h39, h5, hlam]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          rcases p22_3 (m.d 0 2) (by simp) with h46 | h46
                          · rcases p22_3 (m.d 1 2) (by simp) with h47 | h47
                            · rcases p22_3 (m.d 2 3) (by simp) with h48 | h48
                              · linarith only [h48, h8, hlam]
                              · linarith only [h15, h48, hlam]
                            · linarith only [h47, hlam, p22_0]
                          · linarith only [h0, h46, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h4, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h8, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h14, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22_1, u2elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p22_1, u2elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h5, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h9, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h14, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h16, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hc02, hlam, hphi, p22_1, u2elo4]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h10, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h15, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h15, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22_1, u2elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                  · linarith only [h1, h12, h14, h15, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h69 | h69
                  · linarith only [h14, h4, h6, h69, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                      · rcases h2bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [hc12, hlam, hphi, p73_1, u2elo0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          rcases p73_3 (m.d 0 2) (by simp) with h76 | h76
                          · rcases p73_3 (m.d 1 2) (by simp) with h77 | h77
                            · linarith only [h0, h77, hlam]
                            · linarith only [h77, h8, hlam]
                          · linarith only [h76, hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h71, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p73_1, u2elo0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          rcases p73_3 (m.d 0 2) (by simp) with h82 | h82
                          · rcases p73_3 (m.d 1 2) (by simp) with h83 | h83
                            · linarith only [h0, h83, hlam]
                            · linarith only [h10, h83, hlam]
                          · linarith only [h82, hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h0, hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          rcases p73_3 (m.d 0 2) (by simp) with h89 | h89
                          · rcases p73_3 (m.d 1 2) (by simp) with h90 | h90
                            · rcases p73_3 (m.d 2 3) (by simp) with h91 | h91
                              · linarith only [h91, hlam, p73_0]
                              · rcases p73_3 (m.d 2 4) (by simp) with h93 | h93
                                · linarith only [h9, h93, hlam]
                                · linarith only [h14, h93, hlam]
                            · linarith only [h90, hlam, p73_0]
                          · linarith only [h4, h89, hlam]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h71, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p73_1, u2elo1]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          rcases p73_3 (m.d 0 2) (by simp) with h99 | h99
                          · rcases p73_3 (m.d 1 2) (by simp) with h100 | h100
                            · rcases p73_3 (m.d 2 3) (by simp) with h101 | h101
                              · linarith only [h101, h8, hlam]
                              · rcases p73_3 (m.d 2 4) (by simp) with h103 | h103
                                · linarith only [h103, h9, hlam]
                                · linarith only [h103, h71, hlam]
                            · linarith only [h100, hlam, p73_0]
                          · linarith only [h0, h99, hlam, p73_1]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h4, hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h8, hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h14, hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h69, hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h5, hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h9, hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p73_1, u2elo0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h1, h11, h14, hc01, hc25, hlam, hphi, ht0b, ht5b, p73_1]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h1, h11, h4, h69, h72, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p73_1, u2elo4]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h10, hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h1, h11, h4, h69, h72, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p73_1, u2elo0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [h71, hlam, p73_0]
                        · have p73_0 := h73c.1
                          have p73_1 := h73c.2.1
                          have p73_2 := h73c.2.2.1
                          have p73_3 := h73c.2.2.2
                          linarith only [hlam, p73_0]
                      · linarith only [h1, h11, h13, h14, h4, h72, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
                      · linarith only [h124, h4, h6, h71, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · linarith only [h124, h14, h4, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                · rcases m.htr 2 3 5 (by decide) (by decide) with h128 | h128
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h129 | h129
                    · linarith only [h129, h13, h9, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
                      · linarith only [h127, h13, h131, h9, hlam]
                      · rcases h2bigk with h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [hlam, p133_0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [hc12, hlam, hphi, p133_1, u2elo0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h128, h131, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p133_1, u2elo0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          rcases p133_3 (m.d 0 2) (by simp) with h137 | h137
                          · rcases p133_3 (m.d 1 2) (by simp) with h138 | h138
                            · linarith only [h0, h138, hlam]
                            · linarith only [h138, h9, hlam]
                          · linarith only [h137, hlam, p133_0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          rcases p133_3 (m.d 0 2) (by simp) with h142 | h142
                          · rcases p133_3 (m.d 1 2) (by simp) with h143 | h143
                            · linarith only [h0, h143, hlam]
                            · linarith only [h10, h143, hlam]
                          · linarith only [h142, hlam, p133_0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h0, hlam, p133_0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [hlam, p133_0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h128, h131, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p133_1, u2elo1]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          rcases p133_3 (m.d 0 2) (by simp) with h150 | h150
                          · rcases p133_3 (m.d 1 2) (by simp) with h151 | h151
                            · rcases p133_3 (m.d 2 3) (by simp) with h152 | h152
                              · linarith only [h152, h8, hlam]
                              · linarith only [h127, h152, hlam]
                            · linarith only [h151, hlam, p133_0]
                          · linarith only [h150, h5, hlam]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          rcases p133_3 (m.d 0 2) (by simp) with h157 | h157
                          · rcases p133_3 (m.d 1 2) (by simp) with h158 | h158
                            · rcases p133_3 (m.d 2 3) (by simp) with h159 | h159
                              · linarith only [h159, h8, hlam]
                              · linarith only [h128, h159, hlam]
                            · linarith only [h158, hlam, p133_0]
                          · linarith only [h0, h157, hlam, p133_1]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h4, hlam, p133_0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h8, hlam, p133_0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [hlam, p133_0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p133_1, u2elo0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h0, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p133_1, u2elo0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h5, hlam, p133_0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h9, hlam, p133_0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h127, hlam, p133_1]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [hlam, p133_0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h129, hlam, p133_1]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [hc02, hlam, hphi, p133_1, u2elo4]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h10, hlam, p133_0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h128, hlam, p133_1]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [h0, h10, h127, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p133_1, u2elo0]
                        · have p133_0 := h133c.1
                          have p133_1 := h133c.2.1
                          have p133_2 := h133c.2.2.1
                          have p133_3 := h133c.2.2.2
                          linarith only [hlam, p133_0]
                  · linarith only [h12, h127, h128, h13, h4, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · linarith only [h11, h127, h13, h4, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h181 | h181
              · linarith only [h11, h12, h181, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                · rcases m.htr 2 3 5 (by decide) (by decide) with h184 | h184
                  · linarith only [h12, h184, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h186 | h186
                    · linarith only [h181, h186, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                      · linarith only [h181, h183, h188, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h12, h183, h188, h4, h6, h7, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · linarith only [h11, h12, h183, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
            · linarith only [h11, h192, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
              · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                · linarith only [h11, h195, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h197 | h197
                  · linarith only [h192, h197, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h199 | h199
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h200 | h200
                      · rcases h2bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hc12, hlam, hphi, p201_1, u2elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          rcases p201_3 (m.d 0 2) (by simp) with h204 | h204
                          · rcases p201_3 (m.d 1 2) (by simp) with h205 | h205
                            · linarith only [h0, h205, hlam]
                            · linarith only [h205, h8, hlam]
                          · linarith only [h204, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h199, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p201_1, u2elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          rcases p201_3 (m.d 0 2) (by simp) with h210 | h210
                          · rcases p201_3 (m.d 1 2) (by simp) with h211 | h211
                            · linarith only [h0, h211, hlam]
                            · linarith only [h10, h211, hlam]
                          · linarith only [h210, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h0, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          rcases p201_3 (m.d 0 2) (by simp) with h217 | h217
                          · rcases p201_3 (m.d 1 2) (by simp) with h218 | h218
                            · rcases p201_3 (m.d 2 3) (by simp) with h219 | h219
                              · linarith only [h219, hlam, p201_0]
                              · rcases p201_3 (m.d 2 4) (by simp) with h221 | h221
                                · linarith only [h221, h9, hlam]
                                · linarith only [h195, h221, hlam]
                            · linarith only [h218, hlam, p201_0]
                          · linarith only [h217, h4, hlam]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h199, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p201_1, u2elo1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          rcases p201_3 (m.d 0 2) (by simp) with h227 | h227
                          · rcases p201_3 (m.d 1 2) (by simp) with h228 | h228
                            · rcases p201_3 (m.d 2 3) (by simp) with h229 | h229
                              · linarith only [h229, h8, hlam]
                              · rcases p201_3 (m.d 2 4) (by simp) with h231 | h231
                                · linarith only [h231, h9, hlam]
                                · linarith only [h199, h231, hlam]
                            · linarith only [h228, hlam, p201_0]
                          · linarith only [h0, h227, hlam, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h4, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h8, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h195, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h197, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h5, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h9, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p201_1, u2elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p201_1, u2elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hc02, hlam, hphi, p201_1, u2elo4]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h10, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h0, h10, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p201_1, u2elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h199, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                      · linarith only [h11, h200, h4, h6, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h11, h194, h199, h4, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h253 | h253
                · linarith only [h11, h253, h8, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h255 | h255
                  · linarith only [h11, h192, h194, h255, h4, h6, h7, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h257 | h257
                    · linarith only [h194, h257, h9, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h259 | h259
                      · linarith only [h11, h194, h259, h4, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h11, h259, h4, h6, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h262 | h262
          · rcases m.htr 1 3 5 (by decide) (by decide) with h263 | h263
            · linarith only [h10, h263, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h265 | h265
              · linarith only [h10, h265, h9, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                · linarith only [h10, h265, h267, h4, h6, h7, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · linarith only [h10, h262, h265, h267, h4, h6, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h270 | h270
            · linarith only [h262, h270, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h272 | h272
              · linarith only [h10, h272, h9, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                · linarith only [h262, h272, h274, h4, h6, h7, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h276 | h276
                  · linarith only [h10, h270, h274, h276, h9, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h278 | h278
                    · linarith only [h10, h272, h278, h9, hlam]
                    · linarith only [h10, h278, h4, h6, h7, hc12, hlam, hphi, u2elo0]
      · linarith only [h5, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
    · linarith only [h4, h8, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
    · rcases m.htr 1 2 4 (by decide) (by decide) with h284 | h284
      · rcases m.htr 1 2 5 (by decide) (by decide) with h285 | h285
        · rcases m.htr 1 3 4 (by decide) (by decide) with h286 | h286
          · rcases m.htr 1 3 5 (by decide) (by decide) with h287 | h287
            · rcases m.htr 1 4 5 (by decide) (by decide) with h288 | h288
              · linarith only [h2, h288, h7, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h290 | h290
                · rcases m.htr 2 3 5 (by decide) (by decide) with h291 | h291
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h292 | h292
                    · linarith only [h2, h284, h292, h7, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h294 | h294
                      · linarith only [h283, h290, h294, h7, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h2bigk with h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [hlam, p296_0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [hc12, hlam, hphi, p296_1, u2elo0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h291, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p296_1, u2elo0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          rcases p296_3 (m.d 0 2) (by simp) with h300 | h300
                          · rcases p296_3 (m.d 1 2) (by simp) with h301 | h301
                            · linarith only [h0, h301, hlam]
                            · linarith only [h284, h301, hlam]
                          · linarith only [h300, hlam, p296_0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          rcases p296_3 (m.d 0 2) (by simp) with h305 | h305
                          · rcases p296_3 (m.d 1 2) (by simp) with h306 | h306
                            · linarith only [h0, h306, hlam]
                            · linarith only [h285, h306, hlam]
                          · linarith only [h305, hlam, p296_0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h0, hlam, p296_0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [hlam, p296_0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h291, h294, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p296_1, u2elo1]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          rcases p296_3 (m.d 0 2) (by simp) with h313 | h313
                          · rcases p296_3 (m.d 1 2) (by simp) with h314 | h314
                            · rcases p296_3 (m.d 2 3) (by simp) with h315 | h315
                              · linarith only [h283, h315, hlam]
                              · linarith only [h290, h315, hlam]
                            · linarith only [h314, hlam, p296_0]
                          · linarith only [h313, h5, hlam]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          rcases p296_3 (m.d 0 2) (by simp) with h320 | h320
                          · rcases p296_3 (m.d 1 2) (by simp) with h321 | h321
                            · rcases p296_3 (m.d 2 3) (by simp) with h322 | h322
                              · linarith only [h283, h322, hlam]
                              · linarith only [h291, h322, hlam]
                            · linarith only [h321, hlam, p296_0]
                          · linarith only [h0, h320, hlam, p296_1]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h4, hlam, p296_0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h283, hlam, p296_0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [hlam, p296_0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h290, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p296_1, u2elo0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h0, h283, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p296_1, u2elo0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h5, hlam, p296_0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h284, hlam, p296_0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h290, hlam, p296_1]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [hlam, p296_0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h292, hlam, p296_1]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [hc02, hlam, hphi, p296_1, u2elo4]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h285, hlam, p296_0]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h291, hlam, p296_1]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [h285, h290, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p296_1, u2elo1]
                        · have p296_0 := h296c.1
                          have p296_1 := h296c.2.1
                          have p296_2 := h296c.2.2.1
                          have p296_3 := h296c.2.2.2
                          linarith only [hlam, p296_0]
                  · linarith only [h1, h287, h290, h291, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h343 | h343
                  · linarith only [h290, h343, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h345 | h345
                    · linarith only [h1, h286, h290, h345, h4, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h347 | h347
                      · linarith only [h2, h286, h347, h7, hlam]
                      · rcases h2bigk with h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [hc12, hlam, hphi, p349_1, u2elo0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          rcases p349_3 (m.d 0 2) (by simp) with h352 | h352
                          · rcases p349_3 (m.d 1 2) (by simp) with h353 | h353
                            · linarith only [h0, h353, hlam]
                            · linarith only [h283, h353, hlam]
                          · linarith only [h352, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          rcases p349_3 (m.d 0 2) (by simp) with h357 | h357
                          · rcases p349_3 (m.d 1 2) (by simp) with h358 | h358
                            · linarith only [h0, h358, hlam]
                            · linarith only [h284, h358, hlam]
                          · linarith only [h357, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          rcases p349_3 (m.d 0 2) (by simp) with h362 | h362
                          · rcases p349_3 (m.d 1 2) (by simp) with h363 | h363
                            · linarith only [h0, h363, hlam]
                            · linarith only [h285, h363, hlam]
                          · linarith only [h362, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h0, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          rcases p349_3 (m.d 0 2) (by simp) with h369 | h369
                          · rcases p349_3 (m.d 1 2) (by simp) with h370 | h370
                            · rcases p349_3 (m.d 2 3) (by simp) with h371 | h371
                              · linarith only [h371, hlam, p349_0]
                              · rcases p349_3 (m.d 2 4) (by simp) with h373 | h373
                                · linarith only [h284, h373, hlam]
                                · linarith only [h290, h373, hlam]
                            · linarith only [h370, hlam, p349_0]
                          · linarith only [h369, h4, hlam]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          rcases p349_3 (m.d 0 2) (by simp) with h378 | h378
                          · rcases p349_3 (m.d 1 2) (by simp) with h379 | h379
                            · rcases p349_3 (m.d 2 3) (by simp) with h380 | h380
                              · linarith only [h283, h380, hlam]
                              · rcases p349_3 (m.d 2 4) (by simp) with h382 | h382
                                · linarith only [h382, hlam, p349_0]
                                · rcases p349_3 (m.d 2 5) (by simp) with h384 | h384
                                  · linarith only [h285, h384, hlam]
                                  · linarith only [h345, h384, hlam]
                            · linarith only [h379, hlam, p349_0]
                          · linarith only [h378, h5, hlam]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          rcases p349_3 (m.d 0 2) (by simp) with h389 | h389
                          · rcases p349_3 (m.d 1 2) (by simp) with h390 | h390
                            · rcases p349_3 (m.d 2 3) (by simp) with h391 | h391
                              · linarith only [h283, h391, hlam]
                              · rcases p349_3 (m.d 2 4) (by simp) with h393 | h393
                                · linarith only [h284, h393, hlam]
                                · rcases p349_3 (m.d 2 5) (by simp) with h395 | h395
                                  · linarith only [h395, hlam, p349_0]
                                  · rcases h4bigk with h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [hlam, p397_0]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h286, h290, h7, hc23, hc45, hlam, hphi, ht34, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h290, h7, hc23, hc45, hlam, hphi, ht34, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h290, h7, hc23, hc45, hlam, hphi, ht34, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h7, hlam, p397_0]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h2, hlam, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [hlam, p397_0]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h2, h290, h7, hc23, hc45, hlam, hphi, ht34, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h2, h290, h7, hc23, hc45, hlam, hphi, ht34, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h288, hlam, p397_0]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h5, hlam, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h284, hlam, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [hlam, p397_0]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h290, hlam, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h345, hlam, p397_0]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h6, hlam, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h286, hlam, p397_0]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h290, h4, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p397_1, u2elo0]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [hlam, p397_0]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h347, hlam, p397_0]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h2, h286, h290, hc23, hc45, hlam, hphi, ht34, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h286, h290, hc23, hc45, hlam, hphi, ht34, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      rcases p397_3 (m.d 0 4) (by simp) with h420 | h420
                                      · linarith only [h420, h7, hlam]
                                      · linarith only [h420, h5, hlam]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [h290, hc23, hc45, hlam, hphi, ht34, p397_1]
                                    · have p397_0 := h397c.1
                                      have p397_1 := h397c.2.1
                                      have p397_2 := h397c.2.2.1
                                      have p397_3 := h397c.2.2.2
                                      linarith only [hlam, p397_0]
                            · linarith only [h390, hlam, p349_0]
                          · linarith only [h389, hc02, hlam, hphi, p349_1, u2elo1]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h4, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h283, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h290, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h343, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h5, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h284, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p349_1, u2elo0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h345, hlam, p349_1]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h0, hc12, hlam, hphi, p349_1, u2elo4]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h285, hlam, p349_0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h1, h287, h343, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p349_1, u2elo0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [h1, h287, h343, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p349_1, u2elo0]
                        · have p349_0 := h349c.1
                          have p349_1 := h349c.2.1
                          have p349_2 := h349c.2.2.1
                          have p349_3 := h349c.2.2.2
                          linarith only [hlam, p349_0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h442 | h442
              · linarith only [h2, h442, h7, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h444 | h444
                · rcases m.htr 2 3 5 (by decide) (by decide) with h445 | h445
                  · linarith only [h0, h283, h287, h445, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h447 | h447
                    · linarith only [h283, h287, h3, h444, h447, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h449 | h449
                      · linarith only [h4, h449, h6, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases h2bigk with h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [hlam, p451_0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h285, h444, h445, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p451_1, u2elo0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h444, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p451_1, u2elo0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          rcases p451_3 (m.d 0 2) (by simp) with h455 | h455
                          · rcases p451_3 (m.d 1 2) (by simp) with h456 | h456
                            · linarith only [h0, h456, hlam]
                            · linarith only [h284, h456, hlam]
                          · linarith only [h455, hlam, p451_0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h444, h445, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p451_1, u2elo0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h0, hlam, p451_0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [hlam, p451_0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h444, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p451_1, u2elo1]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          rcases p451_3 (m.d 0 2) (by simp) with h464 | h464
                          · rcases p451_3 (m.d 1 2) (by simp) with h465 | h465
                            · rcases p451_3 (m.d 2 3) (by simp) with h466 | h466
                              · linarith only [h283, h466, hlam]
                              · linarith only [h444, h466, hlam]
                            · linarith only [h465, hlam, p451_0]
                          · linarith only [h464, h5, hlam]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h0, h444, h445, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p451_1, u2elo0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h4, hlam, p451_0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h283, hlam, p451_0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [hlam, p451_0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h283, h287, h444, h449, hc34, hc45, hlam, hphi, p451_1]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h445, hlam, p451_0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h5, hlam, p451_0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h284, hlam, p451_0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h444, hlam, p451_1]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [hlam, p451_0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h447, hlam, p451_1]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h0, h285, hlam, p451_1]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h285, hlam, p451_0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h0, h285, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p451_1, u2elo0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [h0, h285, h444, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p451_1, u2elo0]
                        · have p451_0 := h451c.1
                          have p451_1 := h451c.2.1
                          have p451_2 := h451c.2.2.1
                          have p451_3 := h451c.2.2.2
                          linarith only [hlam, p451_0]
                · linarith only [h286, h287, h444, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h488 | h488
            · linarith only [h286, h4, h488, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h490 | h490
              · linarith only [h2, h286, h490, h6, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
                · linarith only [h283, h286, h492, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h494 | h494
                  · linarith only [h283, h286, h4, h488, h494, h6, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h496 | h496
                    · linarith only [h283, h286, h496, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h498 | h498
                      · linarith only [h498, h6, h7, hlam]
                      · rcases h2bigk with h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [hc12, hlam, hphi, p500_1, u2elo0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          rcases p500_3 (m.d 0 2) (by simp) with h503 | h503
                          · rcases p500_3 (m.d 1 2) (by simp) with h504 | h504
                            · linarith only [h0, h504, hlam]
                            · linarith only [h283, h504, hlam]
                          · linarith only [h503, hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          rcases p500_3 (m.d 0 2) (by simp) with h508 | h508
                          · rcases p500_3 (m.d 1 2) (by simp) with h509 | h509
                            · linarith only [h0, h509, hlam]
                            · linarith only [h284, h509, hlam]
                          · linarith only [h508, hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          rcases p500_3 (m.d 0 2) (by simp) with h513 | h513
                          · rcases p500_3 (m.d 1 2) (by simp) with h514 | h514
                            · linarith only [h0, h514, hlam]
                            · linarith only [h285, h514, hlam]
                          · linarith only [h513, hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [h0, hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          rcases p500_3 (m.d 0 2) (by simp) with h520 | h520
                          · rcases p500_3 (m.d 1 2) (by simp) with h521 | h521
                            · rcases p500_3 (m.d 2 3) (by simp) with h522 | h522
                              · linarith only [h522, hlam, p500_0]
                              · rcases p500_3 (m.d 2 4) (by simp) with h524 | h524
                                · linarith only [h284, h524, hlam]
                                · linarith only [h492, h524, hlam]
                            · linarith only [h521, hlam, p500_0]
                          · linarith only [h4, h520, hlam]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          rcases p500_3 (m.d 0 2) (by simp) with h529 | h529
                          · rcases p500_3 (m.d 1 2) (by simp) with h530 | h530
                            · rcases p500_3 (m.d 2 3) (by simp) with h531 | h531
                              · linarith only [h283, h531, hlam]
                              · rcases p500_3 (m.d 2 4) (by simp) with h533 | h533
                                · linarith only [h533, hlam, p500_0]
                                · rcases p500_3 (m.d 2 5) (by simp) with h535 | h535
                                  · linarith only [h285, h535, hlam]
                                  · linarith only [h496, h535, hlam]
                            · linarith only [h530, hlam, p500_0]
                          · linarith only [h5, h529, hlam]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          rcases p500_3 (m.d 0 2) (by simp) with h540 | h540
                          · rcases p500_3 (m.d 1 2) (by simp) with h541 | h541
                            · rcases p500_3 (m.d 2 3) (by simp) with h542 | h542
                              · linarith only [h283, h542, hlam]
                              · rcases p500_3 (m.d 2 4) (by simp) with h544 | h544
                                · linarith only [h284, h544, hlam]
                                · rcases p500_3 (m.d 2 5) (by simp) with h546 | h546
                                  · linarith only [h546, hlam, p500_0]
                                  · rcases h4bigk with h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h283, h286, h7, hc23, hc45, hlam, hphi, ht34, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h7, hc24, hc45, hlam, hphi, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h283, h286, h7, hc23, hc45, hlam, hphi, ht34, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h7, hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h2, hlam, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h2, h7, hc24, hc45, hlam, hphi, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h286, hlam, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h490, hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h5, hlam, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h284, hlam, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h492, hlam, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h496, hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h6, hlam, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h4, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p548_1, u2elo0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h4, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p548_1, u2elo0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h498, hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h283, h286, h6, hc23, hc45, hlam, hphi, ht34, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      rcases p548_3 (m.d 0 4) (by simp) with h570 | h570
                                      · linarith only [h570, h7, hlam]
                                      · linarith only [h2, h570, hlam]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      rcases p548_3 (m.d 0 4) (by simp) with h573 | h573
                                      · linarith only [h573, h7, hlam]
                                      · linarith only [h5, h573, hlam]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h283, h286, hc23, hc45, hlam, hphi, ht34, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [hlam, p548_0]
                            · linarith only [h541, hlam, p500_0]
                          · linarith only [h540, hc02, hlam, hphi, p500_1, u2elo1]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [h4, hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [h283, hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [h492, hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [h494, hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [h5, hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [h284, hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p500_1, u2elo0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [h496, hlam, p500_1]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [hc02, hlam, hphi, p500_1, u2elo4]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [h285, hlam, p500_0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [h0, h285, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p500_1, u2elo0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [h0, h285, h492, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p500_1, u2elo0]
                        · have p500_0 := h500c.1
                          have p500_1 := h500c.2.1
                          have p500_2 := h500c.2.2.1
                          have p500_3 := h500c.2.2.2
                          linarith only [hlam, p500_0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h595 | h595
          · rcases m.htr 1 3 5 (by decide) (by decide) with h596 | h596
            · linarith only [h283, h285, h596, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h598 | h598
              · linarith only [h2, h598, h7, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h600 | h600
                · linarith only [h283, h285, h600, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h283, h285, h595, h600, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h603 | h603
            · linarith only [h4, h595, h6, h603, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h605 | h605
              · linarith only [h4, h595, h6, h605, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h607 | h607
                · linarith only [h283, h595, h607, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h609 | h609
                  · linarith only [h283, h285, h595, h6, h603, h609, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h611 | h611
                    · linarith only [h284, h285, h611, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h613 | h613
                      · linarith only [h285, h4, h6, h611, h613, hc12, hlam, hphi, u2elo0]
                      · rcases h2bigk with h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h284, h607, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p615_1, u2elo0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          rcases p615_3 (m.d 0 2) (by simp) with h618 | h618
                          · rcases p615_3 (m.d 1 2) (by simp) with h619 | h619
                            · linarith only [h0, h619, hlam]
                            · linarith only [h283, h619, hlam]
                          · linarith only [h618, hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          rcases p615_3 (m.d 0 2) (by simp) with h623 | h623
                          · rcases p615_3 (m.d 1 2) (by simp) with h624 | h624
                            · linarith only [h0, h624, hlam]
                            · linarith only [h284, h624, hlam]
                          · linarith only [h623, hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h284, h285, h607, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p615_1, u2elo0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h0, hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h285, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p615_1, u2elo4]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h285, h607, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p615_1, u2elo4]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h285, hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h4, hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h283, hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h607, hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h609, hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h5, hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h284, hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p615_1, u2elo0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [hlam, p615_0]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [h611, hlam, p615_1]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [hc02, hlam, hphi, p615_1, u2elo4]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [hc12, hlam, hphi, p615_1, u2elo4]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          rcases p615_3 (m.d 0 2) (by simp) with h646 | h646
                          · rcases p615_3 (m.d 1 2) (by simp) with h647 | h647
                            · linarith only [h285, h647, hlam]
                            · linarith only [h283, h647, hlam]
                          · linarith only [h4, h646, hlam]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          rcases p615_3 (m.d 0 2) (by simp) with h651 | h651
                          · rcases p615_3 (m.d 1 2) (by simp) with h652 | h652
                            · linarith only [h285, h652, hlam]
                            · linarith only [h284, h652, hlam]
                          · linarith only [h5, h651, hlam]
                        · have p615_0 := h615c.1
                          have p615_1 := h615c.2.1
                          have p615_2 := h615c.2.2.1
                          have p615_3 := h615c.2.2.2
                          linarith only [hlam, p615_0]
      · linarith only [h284, h5, hc12, hlam, hphi, u2elo0]
    · linarith only [h283, h4, hc12, hlam, hphi, u2elo0]

end R2N4
