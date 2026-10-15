import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3710000 in
set_option maxHeartbeats 3710000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_0_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                          · linarith only [h0, h13, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h13, h5, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                          · linarith only [h0, h16, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h16, h5, hc23, hlam, hphi, u3elo0]
                      · linarith only [h11, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h10, h5, h7, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
                      · linarith only [h22, h7, h9, hlam]
                      · linarith only [h22, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h21, h5, h7, hc23, hlam, hphi, u3elo0]
                · linarith only [h0, h4, h7, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                              · linarith only [h27, h34, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · linarith only [h2, h31, h34, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h33, h7, hc12, hlam, hphi, ht23, u3elo4]
                          · linarith only [h32, h7, hc12, hlam, hphi, ht23, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                              · linarith only [h1, h27, h31, h41, h7, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                                · linarith only [h27, h31, h39, h43, hlam]
                                · rcases h1bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h28, h41, hc24, hlam, hphi, ht0b, ht45, ht5b, p45_1, u0elo0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h28, h39, h41, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, p45_1, u0elo0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    rcases p45_3 (m.d 0 1) (by simp) with h49 | h49
                                    · rcases p45_3 (m.d 1 2) (by simp) with h50 | h50
                                      · linarith only [h0, h50, hlam]
                                      · linarith only [h27, h50, hlam]
                                    · linarith only [h49, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    rcases p45_3 (m.d 0 1) (by simp) with h54 | h54
                                    · rcases p45_3 (m.d 1 2) (by simp) with h55 | h55
                                      · linarith only [h0, h55, hlam]
                                      · linarith only [h28, h55, hlam]
                                    · linarith only [h54, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h0, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h7, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h27, h39, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p45_1, u3elo2]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p45_1, u3elo2]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h1, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h1, hc12, hlam, hphi, ht23, p45_1, u3elo0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h1, h27, h39, hc34, hlam, hphi, ht0b, ht45, ht5b, p45_1, u0elo0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h1, h28, h39, h41, hc34, hlam, hphi, ht0b, ht45, ht5b, p45_1, u0elo0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h2, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h27, hlam, p45_1]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h29, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h31, hlam, p45_1]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h3, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h28, hlam, p45_1]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h30, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h27, h3, h39, hc34, hlam, hphi, ht0b, ht45, ht5b, p45_1, u0elo0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hlam, p45_0]
                            · linarith only [h40, h6, hc23, hlam, hphi, u3elo0]
                          · linarith only [h39, h7, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h30, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h27, h29, h5, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h83 | h83
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                        · linarith only [h27, h28, h85, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h89 | h89
                              · linarith only [h27, h28, h85, h88, h89, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h91 | h91
                                · linarith only [h28, h89, h91, hc12, hlam, hphi, ht23, u3elo3]
                                · rcases h1bigk with h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h27, h87, hc34, hlam, hphi, ht0b, ht45, ht5b, p93_1, u0elo0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h84, hc35, hlam, hphi, ht0b, ht5b, p93_1, u0elo0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    rcases p93_3 (m.d 0 1) (by simp) with h97 | h97
                                    · rcases p93_3 (m.d 1 2) (by simp) with h98 | h98
                                      · linarith only [h0, h98, hlam]
                                      · linarith only [h27, h98, hlam]
                                    · linarith only [h97, hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h27, h28, h87, hc34, hlam, hphi, ht0b, ht45, ht5b, p93_1, u0elo0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h0, hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h7, hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h28, h88, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p93_1, u3elo2]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h28, hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h1, hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht23, p93_1, u3elo1]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h1, h27, h87, hc34, hlam, hphi, ht0b, ht45, ht5b, p93_1, u0elo0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h1, h27, h28, h87, hc34, hlam, hphi, ht0b, ht45, ht5b, p93_1, u0elo0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h2, hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h27, hlam, p93_1]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h83, hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h85, hlam, p93_1]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h3, hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h27, h3, h87, hc34, hlam, hphi, ht0b, ht45, ht5b, p93_1, u0elo0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h84, hlam, p93_0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [h1, h27, h84, h87, hc34, hlam, hphi, ht0b, ht45, ht5b, p93_1, u0elo0]
                                  · have p93_0 := h93c.1
                                    have p93_1 := h93c.2.1
                                    have p93_2 := h93c.2.2.1
                                    have p93_3 := h93c.2.2.2
                                    linarith only [hlam, p93_0]
                            · linarith only [h6, h88, hc23, hlam, hphi, u3elo0]
                          · linarith only [h7, h87, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h6, h84, hc13, hlam, hphi, u3elo0]
                    · linarith only [h27, h5, h7, h83, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h127 | h127
                  · linarith only [h0, h127, h27, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h130 | h130
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h133 | h133
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
                                · linarith only [h1, h129, h135, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h131, h135, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h131, h134, h27, hlam]
                            · linarith only [h130, h133, h7, hlam]
                          · linarith only [h132, h5, h7, hc13, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h143 | h143
                              · linarith only [h0, h131, h143, h4, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h145 | h145
                                · linarith only [h143, h145, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                                · rcases h1bigk with h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    rcases p147_3 (m.d 0 1) (by simp) with h149 | h149
                                    · rcases p147_3 (m.d 1 2) (by simp) with h150 | h150
                                      · linarith only [h150, hlam, p147_0]
                                      · rcases p147_3 (m.d 1 3) (by simp) with h152 | h152
                                        · linarith only [h1, h152, hlam]
                                        · linarith only [h152, h7, hlam]
                                    · linarith only [h149, hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h129, hc34, hlam, hphi, ht0b, ht45, ht5b, p147_1, u0elo0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    rcases p147_3 (m.d 0 1) (by simp) with h157 | h157
                                    · rcases p147_3 (m.d 1 2) (by simp) with h158 | h158
                                      · linarith only [h0, h158, hlam]
                                      · rcases p147_3 (m.d 1 3) (by simp) with h160 | h160
                                        · linarith only [h1, h160, hlam]
                                        · linarith only [h129, h160, hlam]
                                    · linarith only [h157, hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    rcases p147_3 (m.d 0 1) (by simp) with h164 | h164
                                    · rcases p147_3 (m.d 1 2) (by simp) with h165 | h165
                                      · linarith only [h0, h165, hlam]
                                      · rcases p147_3 (m.d 1 3) (by simp) with h167 | h167
                                        · linarith only [h1, h167, hlam]
                                        · linarith only [h130, h167, hlam]
                                    · linarith only [h164, hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h0, hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h7, hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h27, hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h127, hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h1, hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht23, p147_1, u3elo1]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h1, h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p147_1, u0elo0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p147_1, u0elo0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h2, hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p147_1, u0elo0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h129, hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h131, hlam, p147_1]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h3, hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p147_1, u0elo0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h130, hlam, p147_0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p147_1, u0elo0]
                                  · have p147_0 := h147c.1
                                    have p147_1 := h147c.2.1
                                    have p147_2 := h147c.2.2.1
                                    have p147_3 := h147c.2.2.2
                                    linarith only [hlam, p147_0]
                            · linarith only [h142, h6, hc23, hlam, hphi, u3elo0]
                          · linarith only [h141, h5, h7, hc13, hlam, hphi, u3elo0]
                      · linarith only [h129, h130, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · linarith only [h129, h5, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
              · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                      · linarith only [h199, h6, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h201 | h201
                        · linarith only [h198, h199, h201, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h203 | h203
                          · linarith only [h0, h195, h203, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h203, h5, hc23, hlam, hphi, u3elo0]
                    · linarith only [h198, h5, h6, hc13, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h207 | h207
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h208 | h208
                      · linarith only [h1, h208, h6, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h210 | h210
                        · linarith only [h195, h197, h2, h210, h5, h6, hc23, hlam, hphi, u3elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
                          · linarith only [h0, h195, h212, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1, h207, h212, h6, hc23, hlam, hphi, u3elo4]
                    · linarith only [h207, h5, h6, hc13, hlam, hphi, u3elo4]
                · linarith only [h196, h4, h5, h6, hc12, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h217 | h217
                · rcases m.htr 1 2 5 (by decide) (by decide) with h218 | h218
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
                      · linarith only [h1, h220, h6, hlam]
                      · linarith only [h195, h218, h220, hlam]
                    · linarith only [h195, h217, h219, h5, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h225 | h225
                      · linarith only [h225, h6, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h227 | h227
                        · linarith only [h195, h217, h225, h227, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h229 | h229
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h230 | h230
                            · linarith only [h1, h195, h217, h229, h230, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h195, h217, h229, h230, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h195, h217, h229, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h224, h5, h6, hc13, hlam, hphi, u3elo4]
                · linarith only [h217, h4, h5, h6, hc12, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h236 | h236
            · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
              · rcases m.htr 1 2 4 (by decide) (by decide) with h238 | h238
                · rcases m.htr 1 2 5 (by decide) (by decide) with h239 | h239
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h240 | h240
                    · linarith only [h240, h5, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h243 | h243
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                          · linarith only [h244, h5, hc03, hlam, hphi, u3elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h246 | h246
                            · linarith only [h0, h238, h244, h246, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h1, h242, h246, h5, hc23, hlam, hphi, u3elo3]
                        · linarith only [h240, h242, h243, hlam]
                      · linarith only [h236, h242, h5, hc13, hlam, hphi, u3elo3]
                  · linarith only [h236, h237, h239, h3, h5, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h237, h238, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h253 | h253
                · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h255 | h255
                    · linarith only [h255, h5, hc03, hlam, hphi, u3elo1]
                    · linarith only [h237, h253, h255, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h258 | h258
                    · linarith only [h236, h253, h254, h258, h3, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · linarith only [h237, h253, h258, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h261 | h261
                  · linarith only [h0, h253, h261, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h263 | h263
                    · linarith only [h263, h5, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h265 | h265
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h266 | h266
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                          · linarith only [h1, h265, h267, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · linarith only [h237, h267, hc12, hlam, hphi, ht23, u3elo3]
                        · linarith only [h263, h265, h266, hlam]
                      · linarith only [h236, h265, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h272 | h272
              · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
                · rcases m.htr 1 2 5 (by decide) (by decide) with h274 | h274
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h275 | h275
                    · linarith only [h275, h5, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h277 | h277
                      · linarith only [h1, h236, h277, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h279 | h279
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
                          · linarith only [h1, h272, h280, h5, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h282 | h282
                            · linarith only [h1, h236, h272, h282, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h284 | h284
                              · linarith only [h0, h273, h284, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h2, h279, h284, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h287 | h287
                          · linarith only [h1, h272, h287, h5, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h289 | h289
                            · linarith only [h236, h272, h275, h279, h289, hc03, hc45, hlam, hphi, ht34]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h291 | h291
                              · linarith only [h0, h273, h291, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h293 | h293
                                · linarith only [h273, h279, h287, h293, hc23, hlam, hphi, u3elo3]
                                · rcases h1bigk with h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h274, hc25, hlam, hphi, ht0b, ht5b, p295_1, u0elo0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    rcases p295_3 (m.d 0 1) (by simp) with h298 | h298
                                    · rcases p295_3 (m.d 1 2) (by simp) with h299 | h299
                                      · linarith only [h0, h299, hlam]
                                      · linarith only [h272, h299, hlam]
                                    · linarith only [h298, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    rcases p295_3 (m.d 0 1) (by simp) with h303 | h303
                                    · rcases p295_3 (m.d 1 2) (by simp) with h304 | h304
                                      · linarith only [h0, h304, hlam]
                                      · linarith only [h273, h304, hlam]
                                    · linarith only [h303, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    rcases p295_3 (m.d 0 1) (by simp) with h308 | h308
                                    · rcases p295_3 (m.d 1 2) (by simp) with h309 | h309
                                      · linarith only [h0, h309, hlam]
                                      · linarith only [h274, h309, hlam]
                                    · linarith only [h308, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h0, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h0, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1, u0elo0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h0, h273, h287, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1, u0elo0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h0, h274, h287, h291, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1, u0elo0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h1, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h272, hlam, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h275, hlam, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h277, hlam, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h2, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h273, hlam, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h2, h272, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1, u0elo0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h279, hlam, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h3, hlam, p295_0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h274, hlam, p295_1]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h272, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1, u0elo0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [h0, h274, hc14, hlam, hphi, ht0b, ht45, ht5b, p295_1, u0elo0]
                                  · have p295_0 := h295c.1
                                    have p295_1 := h295c.2.1
                                    have p295_2 := h295c.2.2.1
                                    have p295_3 := h295c.2.2.2
                                    linarith only [hlam, p295_0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h333 | h333
                    · linarith only [h1, h333, h5, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h335 | h335
                      · linarith only [h1, h236, h335, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h337 | h337
                        · linarith only [h273, h274, h337, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h339 | h339
                          · linarith only [h339, h5, hc03, hlam, hphi, u3elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h341 | h341
                            · linarith only [h1, h236, h272, h273, h274, h3, h341, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h273, h274, h339, h341, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h272, h273, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h345 | h345
                · rcases m.htr 1 2 5 (by decide) (by decide) with h346 | h346
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h347 | h347
                    · linarith only [h1, h347, h5, hlam]
                    · linarith only [h272, h345, h347, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h350 | h350
                    · linarith only [h1, h350, h5, hlam]
                    · linarith only [h272, h345, h350, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h353 | h353
                  · linarith only [h0, h345, h353, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                    · linarith only [h1, h355, h5, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h357 | h357
                      · linarith only [h1, h236, h357, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h359 | h359
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h360 | h360
                          · linarith only [h360, h5, hc03, hlam, hphi, u3elo2]
                          · linarith only [h272, h360, hc12, hlam, hphi, ht23, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                          · linarith only [h1, h272, h363, h5, hc12, hlam, hphi, ht23, u3elo2]
                          · linarith only [h272, h363, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h366 | h366
          · rcases m.htr 0 3 5 (by decide) (by decide) with h367 | h367
            · rcases m.htr 1 2 3 (by decide) (by decide) with h368 | h368
              · rcases m.htr 1 2 4 (by decide) (by decide) with h369 | h369
                · linarith only [h0, h369, h4, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
                    · linarith only [h368, h369, h372, hlam]
                    · linarith only [h366, h372, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h375 | h375
                    · linarith only [h368, h369, h375, hlam]
                    · linarith only [h366, h375, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h378 | h378
                · linarith only [h368, h378, h4, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h380 | h380
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h381 | h381
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h382 | h382
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h383 | h383
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h384 | h384
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h385 | h385
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h386 | h386
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h387 | h387
                                · linarith only [h1, h381, h387, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h2, h383, h387, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h1, h381, h383, h386, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h0, h380, h384, h385, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                          · linarith only [h366, h384, hc23, hlam, hphi, u3elo0]
                        · linarith only [h378, h380, h383, hlam]
                      · linarith only [h367, h381, h382, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h366, h368, h380, h381, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h396 | h396
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h397 | h397
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h398 | h398
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h399 | h399
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h400 | h400
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h401 | h401
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h402 | h402
                                · linarith only [h1, h396, h402, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h1, h396, h398, h402, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h1, h396, h398, h4, h401, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h1, h397, h400, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h1, h366, h368, h397, h399, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h409 | h409
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h410 | h410
                              · linarith only [h378, h398, h408, h410, hc12, hlam, hphi, ht23, u3elo2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h412 | h412
                                · linarith only [h1, h396, h412, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · rcases h1bigk with h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    rcases p414_3 (m.d 0 1) (by simp) with h416 | h416
                                    · rcases p414_3 (m.d 1 2) (by simp) with h417 | h417
                                      · linarith only [h417, hlam, p414_0]
                                      · rcases p414_3 (m.d 1 3) (by simp) with h419 | h419
                                        · linarith only [h1, h419, hlam]
                                        · linarith only [h368, h419, hlam]
                                    · linarith only [h416, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h396, hc34, hlam, hphi, ht0b, ht45, ht5b, p414_1, u0elo0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    rcases p414_3 (m.d 0 1) (by simp) with h424 | h424
                                    · rcases p414_3 (m.d 1 2) (by simp) with h425 | h425
                                      · linarith only [h0, h425, hlam]
                                      · rcases p414_3 (m.d 1 3) (by simp) with h427 | h427
                                        · linarith only [h1, h427, hlam]
                                        · linarith only [h396, h427, hlam]
                                    · linarith only [h424, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    rcases p414_3 (m.d 0 1) (by simp) with h431 | h431
                                    · rcases p414_3 (m.d 1 2) (by simp) with h432 | h432
                                      · linarith only [h0, h432, hlam]
                                      · rcases p414_3 (m.d 1 3) (by simp) with h434 | h434
                                        · linarith only [h1, h434, hlam]
                                        · linarith only [h397, h434, hlam]
                                    · linarith only [h431, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h0, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h368, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h378, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h380, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h1, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht23, p414_1, u3elo1]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h1, h378, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p414_1, u0elo0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h1, h378, h398, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p414_1, u0elo0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h2, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p414_1, u0elo0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h396, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h398, hlam, p414_1]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h3, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p414_1, u0elo0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h397, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h1, h397, hc14, hlam, hphi, ht0b, ht45, ht5b, p414_1, u0elo0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [hlam, p414_0]
                            · linarith only [h367, h409, hc23, hlam, hphi, u3elo0]
                          · linarith only [h366, h368, h408, hc13, hlam, hphi, u3elo0]
                      · linarith only [h367, h396, h397, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · linarith only [h366, h368, h396, hc12, hlam, hphi, ht23, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h462 | h462
              · linarith only [h0, h366, h367, h4, h462, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h464 | h464
                · linarith only [h0, h4, h464, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h466 | h466
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h467 | h467
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h468 | h468
                      · linarith only [h366, h367, h4, h468, hc02, hlam, hphi, ht23, u3elo1]
                      · linarith only [h462, h466, h468, hlam]
                    · linarith only [h366, h367, h462, h467, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h472 | h472
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h473 | h473
                      · linarith only [h367, h473, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h475 | h475
                        · linarith only [h472, h473, h475, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h478 | h478
                            · linarith only [h1, h367, h472, h478, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h462, h478, hc12, hlam, hphi, ht23, u3elo4]
                          · linarith only [h1, h367, h462, h472, h477, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h366, h367, h472, hc13, hlam, hphi, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h483 | h483
            · rcases m.htr 1 2 3 (by decide) (by decide) with h484 | h484
              · rcases m.htr 1 2 4 (by decide) (by decide) with h485 | h485
                · linarith only [h0, h4, h485, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h487 | h487
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
                    · linarith only [h366, h483, h488, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h490 | h490
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h491 | h491
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
                          · linarith only [h0, h1, h366, h484, h490, h492, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h0, h4, h484, h492, hc23, hlam, hphi, u3elo3]
                        · linarith only [h3, h366, h483, h484, h485, h491, hc23, hlam, hphi, u3elo3]
                      · linarith only [h366, h483, h490, hc13, hlam, hphi, u3elo3]
                  · linarith only [h3, h366, h483, h484, h487, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h498 | h498
                · linarith only [h4, h484, h498, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h500 | h500
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h501 | h501
                    · linarith only [h1, h366, h501, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h503 | h503
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h504 | h504
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h505 | h505
                          · linarith only [h1, h366, h484, h500, h505, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · linarith only [h484, h500, h505, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h498, h500, h504, hlam]
                      · linarith only [h483, h484, h500, h503, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h510 | h510
                    · linarith only [h366, h510, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h512 | h512
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h513 | h513
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                          · linarith only [h1, h366, h512, h514, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · linarith only [h484, h514, hc12, hlam, hphi, ht23, u3elo3]
                        · linarith only [h510, h512, h513, hlam]
                      · linarith only [h366, h483, h512, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h519 | h519
              · rcases m.htr 1 2 4 (by decide) (by decide) with h520 | h520
                · linarith only [h0, h4, h520, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h522 | h522
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h523 | h523
                    · linarith only [h366, h523, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h525 | h525
                      · linarith only [h1, h483, h525, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h527 | h527
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h528 | h528
                          · linarith only [h2, h366, h519, h520, h528, hlam]
                          · linarith only [h0, h4, h519, h528, hc23, hlam, hphi, u3elo3]
                        · linarith only [h520, h522, h527, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h532 | h532
                    · linarith only [h1, h366, h532, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h534 | h534
                      · linarith only [h1, h483, h534, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h536 | h536
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h537 | h537
                          · linarith only [h0, h519, h537, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h4, h519, h537, hc23, hlam, hphi, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h540 | h540
                          · linarith only [h3, h519, h520, h536, h540, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h4, h519, h540, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h543 | h543
                · linarith only [h4, h519, h543, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h545 | h545
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h546 | h546
                    · linarith only [h1, h366, h546, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h548 | h548
                      · linarith only [h1, h483, h548, hlam]
                      · linarith only [h519, h545, h548, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h551 | h551
                    · linarith only [h366, h551, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h553 | h553
                      · linarith only [h1, h483, h553, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h555 | h555
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h556 | h556
                          · linarith only [h366, h556, hc03, hlam, hphi, u3elo2]
                          · linarith only [h519, h556, hc12, hlam, hphi, ht23, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h559 | h559
                          · linarith only [h1, h366, h519, h559, hc12, hlam, hphi, ht23, u3elo2]
                          · linarith only [h519, h559, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h562 | h562
        · rcases m.htr 0 3 4 (by decide) (by decide) with h563 | h563
          · rcases m.htr 0 3 5 (by decide) (by decide) with h564 | h564
            · linarith only [h1, h3, h564, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h566 | h566
              · linarith only [h0, h3, h564, h566, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h568 | h568
                · rcases m.htr 1 2 5 (by decide) (by decide) with h569 | h569
                  · linarith only [h1, h3, h566, h569, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h571 | h571
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h572 | h572
                      · linarith only [h1, h3, h564, h572, hlam]
                      · linarith only [h1, h3, h566, h568, h572, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h563, h564, h566, h568, h571, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h562, h563, h564, h568, hc12, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h577 | h577
            · linarith only [h0, h3, h563, h577, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h579 | h579
              · linarith only [h0, h3, h577, h579, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h581 | h581
                · rcases m.htr 1 2 5 (by decide) (by decide) with h582 | h582
                  · linarith only [h1, h3, h579, h582, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h584 | h584
                    · linarith only [h1, h3, h563, h577, h584, hc03, hlam, hphi, u3elo4]
                    · linarith only [h579, h581, h584, hlam]
                · linarith only [h0, h3, h562, h577, h581, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h588 | h588
          · rcases m.htr 0 3 5 (by decide) (by decide) with h589 | h589
            · linarith only [h1, h3, h589, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h591 | h591
              · linarith only [h0, h562, h588, h589, h591, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h593 | h593
                · linarith only [h0, h562, h593, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h595 | h595
                  · linarith only [h1, h3, h591, h595, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h597 | h597
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h598 | h598
                      · linarith only [h1, h3, h589, h598, hlam]
                      · linarith only [h1, h3, h593, h597, h598, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h588, h591, h597, hc12, hlam, hphi, ht23, u3elo0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h602 | h602
            · linarith only [h1, h3, h602, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
              · linarith only [h0, h3, h602, h604, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h606 | h606
                · linarith only [h0, h562, h606, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h608 | h608
                  · linarith only [h1, h3, h604, h608, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h610 | h610
                    · linarith only [h1, h3, h588, h602, h610, hc03, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h612 | h612
                      · linarith only [h2, h3, h602, h610, h612, hlam]
                      · linarith only [h2, h3, h604, h610, h612, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h615 | h615
      · rcases m.htr 0 2 4 (by decide) (by decide) with h616 | h616
        · linarith only [h0, h2, h616, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h618 | h618
          · linarith only [h1, h2, h618, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h620 | h620
            · rcases m.htr 1 2 3 (by decide) (by decide) with h621 | h621
              · linarith only [h0, h2, h618, h621, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h623 | h623
                · linarith only [h1, h2, h616, h618, h621, h623, hc02, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h625 | h625
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h626 | h626
                    · linarith only [h1, h2, h618, h626, hlam]
                    · linarith only [h1, h2, h621, h626, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h629 | h629
                    · linarith only [h1, h618, h629, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h1, h2, h621, h629, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h632 | h632
              · linarith only [h0, h2, h618, h632, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h634 | h634
                · linarith only [h1, h2, h616, h632, h634, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h636 | h636
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h637 | h637
                    · linarith only [h1, h2, h618, h637, hlam]
                    · linarith only [h1, h2, h632, h637, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h640 | h640
                    · linarith only [h1, h618, h640, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h2, h615, h636, h640, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h643 | h643
        · linarith only [h0, h2, h643, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h645 | h645
          · linarith only [h1, h2, h645, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h647 | h647
            · linarith only [h1, h615, h645, h647, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h649 | h649
              · linarith only [h0, h2, h645, h649, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h651 | h651
                · linarith only [h1, h2, h643, h645, h649, h651, hc02, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h653 | h653
                  · linarith only [h1, h615, h649, h653, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h655 | h655
                    · linarith only [h1, h2, h645, h655, hlam]
                    · linarith only [h1, h2, h649, h655, hc12, hlam, hphi, ht23, u3elo3]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
