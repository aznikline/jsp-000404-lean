import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                              · linarith only [h0, h10, h16, h19, hc01, hc45, hlam, hphi, ht0b, ht5b]
                              · linarith only [h19, h9, hc34, hlam, hphi, u4elo0]
                            · linarith only [h15, h18, h2, hc24, hlam, hphi, u4elo0]
                          · linarith only [h0, h10, h14, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                          · linarith only [h1, h13, h16, h24, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                              · rcases h0bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h1, h13, h24, h27, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h1, h13, h24, h27, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h26, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h24, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h0, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h1, h13, h24, h27, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h0, h24, h27, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h0, h24, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h1, hlam, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h4, hlam, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h24, h27, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h0, h24, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h2, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h5, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h7, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h24, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h3, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h6, hlam, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h8, hlam, p28_0]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [h9, hlam, p28_1]
                                · have p28_0 := h28c.1
                                  have p28_1 := h28c.2.1
                                  have p28_2 := h28c.2.2.1
                                  have p28_3 := h28c.2.2.2
                                  linarith only [hlam, p28_0]
                              · linarith only [h26, h27, hc34, hlam, hphi, u4elo2]
                            · linarith only [h26, h9, hc24, hlam, hphi, u4elo0]
                      · linarith only [h15, h9, hc14, hlam, hphi, u4elo0]
                    · linarith only [h13, h14, h8, h9, hc34, hlam, hphi, u4elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                        · linarith only [h0, h13, h4, h58, h60, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                              · rcases h0bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h1, h10, h4, h62, h64, hc01, hc45, hlam, hphi, ht0b, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h1, h10, h62, h64, hc01, hc45, hlam, hphi, ht0b, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h10, h13, h62, h64, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  rcases p65_3 (m.d 0 1) (by simp) with h70 | h70
                                  · rcases p65_3 (m.d 0 2) (by simp) with h71 | h71
                                    · linarith only [h0, h71, hlam]
                                    · linarith only [h6, h71, hlam]
                                  · linarith only [h3, h70, hlam]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h0, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h10, h13, h62, h64, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h0, h10, h13, h62, h64, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  rcases p65_3 (m.d 0 1) (by simp) with h79 | h79
                                  · rcases p65_3 (m.d 0 2) (by simp) with h80 | h80
                                    · rcases p65_3 (m.d 0 3) (by simp) with h81 | h81
                                      · linarith only [h4, h81, hlam]
                                      · linarith only [h8, h81, hlam]
                                    · linarith only [h6, h80, hlam]
                                  · linarith only [h3, h79, hlam]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h1, hlam, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h4, hlam, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h10, h13, h62, h64, h7, hc03, hc45, hlam, hphi, ht0b, ht5b, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  rcases p65_3 (m.d 0 1) (by simp) with h90 | h90
                                  · rcases p65_3 (m.d 0 2) (by simp) with h91 | h91
                                    · rcases p65_3 (m.d 0 3) (by simp) with h92 | h92
                                      · rcases p65_3 (m.d 0 4) (by simp) with h93 | h93
                                        · linarith only [h7, h93, hlam]
                                        · linarith only [h9, h93, hlam]
                                      · linarith only [h8, h92, hlam]
                                    · linarith only [h6, h91, hlam]
                                  · linarith only [h3, h90, hlam]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h2, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h5, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h7, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p65_1, u4elo0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h3, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h6, hlam, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h8, hlam, p65_0]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [h9, hlam, p65_1]
                                · have p65_0 := h65c.1
                                  have p65_1 := h65c.2.1
                                  have p65_2 := h65c.2.2.1
                                  have p65_3 := h65c.2.2.2
                                  linarith only [hlam, p65_0]
                              · linarith only [h13, h64, hc13, hlam, hphi, ht34, u4elo4]
                            · linarith only [h59, h60, h62, h63, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                          · linarith only [h13, h58, h62, h7, hc23, hlam, hphi, ht34, u4elo0]
                      · linarith only [h59, h9, hc14, hlam, hphi, u4elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
                        · linarith only [h10, h114, h58, h8, h9, hc34, hlam, hphi, u4elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h116 | h116
                          · linarith only [h114, h116, h58, hc13, hlam, hphi, ht34, u4elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h118 | h118
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h119 | h119
                              · rcases h0bigk with h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [hlam, p120_0]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h11, h118, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h10, h58, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h0, hlam, p120_0]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [hlam, p120_0]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h10, h13, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h0, h10, h13, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h0, h10, h58, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h1, hlam, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h4, hlam, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [hlam, p120_0]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h10, h13, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h0, h10, h4, h58, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h2, hlam, p120_0]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h5, hlam, p120_0]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h7, hlam, p120_0]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [hlam, p120_0]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p120_1, u4elo0]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h3, hlam, p120_0]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h6, hlam, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h8, hlam, p120_0]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [h9, hlam, p120_1]
                                · have p120_0 := h120c.1
                                  have p120_1 := h120c.2.1
                                  have p120_2 := h120c.2.2.1
                                  have p120_3 := h120c.2.2.2
                                  linarith only [hlam, p120_0]
                              · linarith only [h10, h11, h118, h119, h13, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h118, h9, hc24, hlam, hphi, u4elo0]
                      · linarith only [h113, h9, hc14, hlam, hphi, u4elo0]
                · linarith only [h10, h12, h6, h9, hc23, hlam, hphi, ht34, u4elo0]
              · linarith only [h10, h11, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
              · rcases m.htr 1 2 5 (by decide) (by decide) with h152 | h152
                · rcases m.htr 1 3 4 (by decide) (by decide) with h153 | h153
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h157 | h157
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h158 | h158
                            · linarith only [h0, h10, h151, h158, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h155, h158, hc24, hlam, hphi, u4elo1]
                          · linarith only [h0, h10, h152, h157, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h10, h156, hc12, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h155, h9, hc14, hlam, hphi, u4elo0]
                    · linarith only [h10, h151, h154, h8, h9, hc24, hlam, hphi, u4elo0]
                  · linarith only [h10, h151, h153, hc24, hlam, hphi, u4elo3]
                · linarith only [h151, h152, h6, h9, hc24, hlam, hphi, u4elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
                · rcases m.htr 1 3 4 (by decide) (by decide) with h168 | h168
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h169 | h169
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h170 | h170
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h171 | h171
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h172 | h172
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h173 | h173
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h174 | h174
                              · rcases h0bigk with h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [hlam, p175_0]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h0, h167, h172, h174, hc01, hc45, hlam, hphi, ht0b, ht5b, p175_1]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h1, h168, h174, hc01, hc45, hlam, hphi, ht0b, ht5b, p175_1]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h151, h167, h172, h174, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p175_1]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  rcases p175_3 (m.d 0 1) (by simp) with h180 | h180
                                  · rcases p175_3 (m.d 0 2) (by simp) with h181 | h181
                                    · linarith only [h0, h181, hlam]
                                    · linarith only [h181, h6, hlam]
                                  · linarith only [h180, h3, hlam]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h0, hlam, p175_0]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [hlam, p175_0]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h151, h167, h171, h172, h174, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p175_1]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h0, h151, h167, h172, h174, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p175_1]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  rcases p175_3 (m.d 0 1) (by simp) with h189 | h189
                                  · rcases p175_3 (m.d 0 2) (by simp) with h190 | h190
                                    · rcases p175_3 (m.d 0 3) (by simp) with h191 | h191
                                      · linarith only [h191, h4, hlam]
                                      · linarith only [h191, h8, hlam]
                                    · linarith only [h190, h6, hlam]
                                  · linarith only [h189, h3, hlam]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h1, hlam, p175_1]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h4, hlam, p175_1]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [hlam, p175_0]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h151, h167, h172, h174, h5, hc03, hc45, hlam, hphi, ht0b, ht5b, p175_1]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  rcases p175_3 (m.d 0 1) (by simp) with h200 | h200
                                  · rcases p175_3 (m.d 0 2) (by simp) with h201 | h201
                                    · rcases p175_3 (m.d 0 3) (by simp) with h202 | h202
                                      · rcases p175_3 (m.d 0 4) (by simp) with h203 | h203
                                        · linarith only [h203, h7, hlam]
                                        · linarith only [h203, h9, hlam]
                                      · linarith only [h202, h8, hlam]
                                    · linarith only [h201, h6, hlam]
                                  · linarith only [h200, h3, hlam]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h2, hlam, p175_0]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h5, hlam, p175_0]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h7, hlam, p175_0]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [hlam, p175_0]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p175_1, u4elo0]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h3, hlam, p175_0]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h6, hlam, p175_1]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h8, hlam, p175_0]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [h9, hlam, p175_1]
                                · have p175_0 := h175c.1
                                  have p175_1 := h175c.2.1
                                  have p175_2 := h175c.2.2.1
                                  have p175_3 := h175c.2.2.2
                                  linarith only [hlam, p175_0]
                              · linarith only [h174, h9, hc34, hlam, hphi, u4elo0]
                            · linarith only [h151, h173, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h0, h151, h167, h171, h172, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h10, h167, h168, h171, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h151, h167, h170, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                    · linarith only [h168, h169, h8, h9, hc34, hlam, hphi, u4elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h225 | h225
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h226 | h226
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                        · linarith only [h0, h168, h225, h227, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h10, h167, h227, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h10, h167, h168, h226, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                    · linarith only [h10, h167, h225, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h233 | h233
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h234 | h234
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h235 | h235
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h236 | h236
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h237 | h237
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h238 | h238
                              · rcases h0bigk with h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h1, h232, h238, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h1, h232, h238, hc01, hc45, hlam, hphi, ht0b, ht5b, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h238, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h167, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h0, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h10, h232, h238, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h0, h151, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h0, h167, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h1, hlam, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h4, hlam, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h151, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h0, h167, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h2, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h5, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h7, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h167, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h3, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h6, hlam, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h8, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h9, hlam, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [hlam, p239_0]
                              · linarith only [h238, h9, hc34, hlam, hphi, u4elo0]
                            · linarith only [h151, h234, h237, hlam]
                          · linarith only [h10, h233, h236, hlam]
                        · linarith only [h10, h235, h7, hc12, hlam, hphi, ht23, ht34, u4elo0]
                      · linarith only [h234, h9, hc14, hlam, hphi, u4elo0]
                    · linarith only [h232, h233, h8, h9, hc34, hlam, hphi, u4elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h271 | h271
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h272 | h272
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h273 | h273
                        · linarith only [h0, h232, h271, h273, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h10, h273, hc12, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h232, h271, h272, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h278 | h278
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h279 | h279
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h280 | h280
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h281 | h281
                              · rcases h0bigk with h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [hlam, p282_0]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h10, h271, h278, h281, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h10, h271, h278, h281, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h2, h277, hc01, hc45, hlam, hphi, ht0b, ht5b, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h10, h271, h279, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h0, hlam, p282_0]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [hlam, p282_0]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h10, h271, h278, h281, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h0, h10, h271, h279, h280, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h0, h10, h271, h279, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h1, hlam, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h4, hlam, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [hlam, p282_0]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h10, h271, h279, h280, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h0, h10, h271, h279, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h2, hlam, p282_0]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h5, hlam, p282_0]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h7, hlam, p282_0]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [hlam, p282_0]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h10, h271, h279, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h3, hlam, p282_0]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h6, hlam, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h8, hlam, p282_0]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [h9, hlam, p282_1]
                                · have p282_0 := h282c.1
                                  have p282_1 := h282c.2.1
                                  have p282_2 := h282c.2.2.1
                                  have p282_3 := h282c.2.2.2
                                  linarith only [hlam, p282_0]
                              · linarith only [h277, h281, hc34, hlam, hphi, u4elo1]
                            · linarith only [h280, h9, hc24, hlam, hphi, u4elo0]
                          · linarith only [h0, h232, h277, h278, h279, h4, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h10, h278, hc12, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h277, h9, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h313 | h313
            · rcases m.htr 1 2 4 (by decide) (by decide) with h314 | h314
              · rcases m.htr 1 2 5 (by decide) (by decide) with h315 | h315
                · rcases m.htr 1 3 4 (by decide) (by decide) with h316 | h316
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h317 | h317
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h318 | h318
                      · linarith only [h2, h318, h9, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h321 | h321
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h322 | h322
                            · linarith only [h322, h9, hc04, hlam, hphi, u4elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h324 | h324
                              · linarith only [h2, h314, h320, h324, h9, hlam]
                              · rcases h0bigk with h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [hlam, p326_0]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h0, h313, h321, h324, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h1, h313, h321, h324, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  rcases p326_3 (m.d 0 1) (by simp) with h330 | h330
                                  · rcases p326_3 (m.d 0 2) (by simp) with h331 | h331
                                    · linarith only [h0, h331, hlam]
                                    · linarith only [h331, h5, hlam]
                                  · linarith only [h2, h330, hlam]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  rcases p326_3 (m.d 0 1) (by simp) with h335 | h335
                                  · rcases p326_3 (m.d 0 2) (by simp) with h336 | h336
                                    · linarith only [h0, h336, hlam]
                                    · linarith only [h336, h6, hlam]
                                  · linarith only [h3, h335, hlam]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h0, hlam, p326_0]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [hlam, p326_0]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h1, h313, h321, h324, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  rcases p326_3 (m.d 0 1) (by simp) with h343 | h343
                                  · rcases p326_3 (m.d 0 2) (by simp) with h344 | h344
                                    · rcases p326_3 (m.d 0 3) (by simp) with h345 | h345
                                      · linarith only [h345, h4, hlam]
                                      · linarith only [h345, h7, hlam]
                                    · linarith only [h344, h5, hlam]
                                  · linarith only [h2, h343, hlam]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  rcases p326_3 (m.d 0 1) (by simp) with h350 | h350
                                  · rcases p326_3 (m.d 0 2) (by simp) with h351 | h351
                                    · rcases p326_3 (m.d 0 3) (by simp) with h352 | h352
                                      · linarith only [h352, h4, hlam]
                                      · linarith only [h352, h8, hlam]
                                    · linarith only [h351, h6, hlam]
                                  · linarith only [h3, h350, hlam]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h1, hlam, p326_1]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h4, hlam, p326_1]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [hlam, p326_0]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  rcases p326_3 (m.d 0 1) (by simp) with h360 | h360
                                  · rcases p326_3 (m.d 0 2) (by simp) with h361 | h361
                                    · rcases p326_3 (m.d 0 3) (by simp) with h362 | h362
                                      · rcases p326_3 (m.d 0 4) (by simp) with h363 | h363
                                        · linarith only [h363, h7, hlam]
                                        · rcases p326_3 (m.d 0 5) (by simp) with h365 | h365
                                          · linarith only [h365, h8, hlam]
                                          · linarith only [h365, h9, hlam]
                                      · linarith only [h362, h7, hlam]
                                    · linarith only [h361, h5, hlam]
                                  · linarith only [h2, h360, hlam]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  rcases p326_3 (m.d 0 1) (by simp) with h371 | h371
                                  · rcases p326_3 (m.d 0 2) (by simp) with h372 | h372
                                    · rcases p326_3 (m.d 0 3) (by simp) with h373 | h373
                                      · rcases p326_3 (m.d 0 4) (by simp) with h374 | h374
                                        · linarith only [h374, h7, hlam]
                                        · rcases p326_3 (m.d 0 5) (by simp) with h376 | h376
                                          · linarith only [h376, h8, hlam]
                                          · rcases h1bigk with h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [hlam, p378_0]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h313, h321, h324, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p378_1]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              rcases p378_3 (m.d 0 1) (by simp) with h381 | h381
                                              · rcases p378_3 (m.d 1 2) (by simp) with h382 | h382
                                                · linarith only [h0, h382, hlam]
                                                · linarith only [h313, h382, hlam]
                                              · linarith only [h381, hlam, p378_0]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h0, h2, h4, h9, hlam, p326_1, p378_2]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h0, h3, h4, hlam, p326_1, p378_2]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h0, hlam, p378_0]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [hlam, p378_0]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h0, h313, h321, hc01, hc35, hlam, hphi, ht0b, ht5b, p378_1]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              rcases p378_3 (m.d 0 1) (by simp) with h391 | h391
                                              · rcases p378_3 (m.d 1 2) (by simp) with h392 | h392
                                                · rcases p378_3 (m.d 1 3) (by simp) with h393 | h393
                                                  · linarith only [h313, h393, hlam]
                                                  · linarith only [h316, h393, hlam]
                                                · linarith only [h314, h392, hlam]
                                              · linarith only [h2, h391, hlam]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              rcases p378_3 (m.d 0 1) (by simp) with h398 | h398
                                              · rcases p378_3 (m.d 1 2) (by simp) with h399 | h399
                                                · rcases p378_3 (m.d 1 3) (by simp) with h400 | h400
                                                  · linarith only [h313, h400, hlam]
                                                  · linarith only [h317, h400, hlam]
                                                · linarith only [h315, h399, hlam]
                                              · linarith only [h3, h398, hlam]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h1, hlam, p378_0]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h313, hlam, p378_1]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [hlam, p378_0]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              rcases p378_3 (m.d 0 1) (by simp) with h408 | h408
                                              · rcases p378_3 (m.d 1 2) (by simp) with h409 | h409
                                                · rcases p378_3 (m.d 1 3) (by simp) with h410 | h410
                                                  · rcases p378_3 (m.d 1 4) (by simp) with h411 | h411
                                                    · linarith only [h316, h411, hlam]
                                                    · rcases p378_3 (m.d 1 5) (by simp) with h413 | h413
                                                      · linarith only [h317, h413, hlam]
                                                      · linarith only [h318, h413, hlam]
                                                  · linarith only [h316, h410, hlam]
                                                · linarith only [h314, h409, hlam]
                                              · linarith only [h2, h408, hlam]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              rcases p378_3 (m.d 0 1) (by simp) with h419 | h419
                                              · rcases p378_3 (m.d 1 2) (by simp) with h420 | h420
                                                · rcases p378_3 (m.d 1 3) (by simp) with h421 | h421
                                                  · rcases p378_3 (m.d 1 4) (by simp) with h422 | h422
                                                    · linarith only [h316, h422, hlam]
                                                    · rcases p378_3 (m.d 1 5) (by simp) with h424 | h424
                                                      · linarith only [h317, h424, hlam]
                                                      · rcases h3bigk with h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h4, hc02, hc15, hlam, hphi, ht0b, ht5b, p378_1, p426_1]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          rcases p426_3 (m.d 0 3) (by simp) with h429 | h429
                                                          · rcases p426_3 (m.d 1 3) (by simp) with h430 | h430
                                                            · linarith only [h1, h430, hlam]
                                                            · linarith only [h313, h430, hlam]
                                                          · linarith only [h4, h429, hlam]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h2, h314, h320, h9, hlam, p326_1, p426_2]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h321, h6, hlam, p326_1, p426_2]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h1, hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h1, h321, hc01, hc35, hlam, hphi, ht0b, ht5b, p426_1]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          rcases p426_3 (m.d 0 3) (by simp) with h439 | h439
                                                          · rcases p426_3 (m.d 1 3) (by simp) with h440 | h440
                                                            · rcases p426_3 (m.d 2 3) (by simp) with h441 | h441
                                                              · linarith only [h313, h441, hlam]
                                                              · linarith only [h320, h441, hlam]
                                                            · linarith only [h440, hlam, p426_0]
                                                          · linarith only [h439, h7, hlam]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          rcases p426_3 (m.d 0 3) (by simp) with h446 | h446
                                                          · rcases p426_3 (m.d 1 3) (by simp) with h447 | h447
                                                            · rcases p426_3 (m.d 2 3) (by simp) with h448 | h448
                                                              · linarith only [h313, h448, hlam]
                                                              · linarith only [h321, h448, hlam]
                                                            · linarith only [h447, hlam, p426_0]
                                                          · linarith only [h446, h8, hlam]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h4, hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h313, hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h0, h313, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p426_1]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h0, h313, h324, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p426_1]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h7, hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h316, hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h320, hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h324, hlam, p426_1]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h8, hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h317, hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h321, hlam, p426_0]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [h8, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1, p426_1]
                                                        · have p426_0 := h426c.1
                                                          have p426_1 := h426c.2.1
                                                          have p426_2 := h426c.2.2.1
                                                          have p426_3 := h426c.2.2.2
                                                          linarith only [hlam, p426_0]
                                                  · linarith only [h317, h421, hlam]
                                                · linarith only [h315, h420, hlam]
                                              · linarith only [h3, h419, hlam]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h2, hlam, p378_0]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h314, hlam, p378_1]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h316, hlam, p378_0]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [hlam, p378_0]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h318, hlam, p378_1]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h3, hlam, p378_0]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h315, hlam, p378_1]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h317, hlam, p378_0]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [h0, h3, h314, h320, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1, p378_1]
                                            · have p378_0 := h378c.1
                                              have p378_1 := h378c.2.1
                                              have p378_2 := h378c.2.2.1
                                              have p378_3 := h378c.2.2.2
                                              linarith only [hlam, p378_0]
                                      · linarith only [h373, h8, hlam]
                                    · linarith only [h372, h6, hlam]
                                  · linarith only [h3, h371, hlam]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h2, hlam, p326_0]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h5, hlam, p326_0]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h7, hlam, p326_0]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [hlam, p326_0]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h9, hlam, p326_0]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h3, hlam, p326_0]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h6, hlam, p326_1]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h8, hlam, p326_0]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [h2, h314, h320, h9, hc34, hlam, hphi, p326_1, u4elo4]
                                · have p326_0 := h326c.1
                                  have p326_1 := h326c.2.1
                                  have p326_2 := h326c.2.2.1
                                  have p326_3 := h326c.2.2.2
                                  linarith only [hlam, p326_0]
                          · linarith only [h0, h313, h317, h320, h321, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h320, h7, h9, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h316, h317, h8, h9, hc34, hlam, hphi, u4elo4]
                  · linarith only [h316, h7, h9, hc13, hlam, hphi, ht34, u4elo4]
                · linarith only [h313, h315, h6, h9, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h313, h314, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h500 | h500
              · rcases m.htr 1 2 5 (by decide) (by decide) with h501 | h501
                · rcases m.htr 1 3 4 (by decide) (by decide) with h502 | h502
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h503 | h503
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h504 | h504
                      · linarith only [h504, h9, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h506 | h506
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h507 | h507
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h508 | h508
                            · linarith only [h2, h500, h508, h9, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h510 | h510
                              · linarith only [h2, h500, h506, h510, h9, hlam]
                              · rcases h0bigk with h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [hlam, p512_0]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h0, h501, h506, h508, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p512_1]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h1, h313, h501, h506, h508, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p512_1]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  rcases p512_3 (m.d 0 1) (by simp) with h516 | h516
                                  · rcases p512_3 (m.d 0 2) (by simp) with h517 | h517
                                    · linarith only [h0, h517, hlam]
                                    · linarith only [h5, h517, hlam]
                                  · linarith only [h2, h516, hlam]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  rcases p512_3 (m.d 0 1) (by simp) with h521 | h521
                                  · rcases p512_3 (m.d 0 2) (by simp) with h522 | h522
                                    · linarith only [h0, h522, hlam]
                                    · linarith only [h522, h6, hlam]
                                  · linarith only [h3, h521, hlam]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h0, hlam, p512_0]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [hlam, p512_0]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h313, h4, h501, h506, h508, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p512_1]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  rcases p512_3 (m.d 0 1) (by simp) with h529 | h529
                                  · rcases p512_3 (m.d 0 2) (by simp) with h530 | h530
                                    · rcases p512_3 (m.d 0 3) (by simp) with h531 | h531
                                      · linarith only [h4, h531, hlam]
                                      · linarith only [h531, h7, hlam]
                                    · linarith only [h5, h530, hlam]
                                  · linarith only [h2, h529, hlam]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  rcases p512_3 (m.d 0 1) (by simp) with h536 | h536
                                  · rcases p512_3 (m.d 0 2) (by simp) with h537 | h537
                                    · rcases p512_3 (m.d 0 3) (by simp) with h538 | h538
                                      · linarith only [h4, h538, hlam]
                                      · linarith only [h538, h8, hlam]
                                    · linarith only [h537, h6, hlam]
                                  · linarith only [h3, h536, hlam]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h1, hlam, p512_1]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h4, hlam, p512_1]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [hlam, p512_0]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  rcases p512_3 (m.d 0 1) (by simp) with h546 | h546
                                  · rcases p512_3 (m.d 0 2) (by simp) with h547 | h547
                                    · rcases p512_3 (m.d 0 3) (by simp) with h548 | h548
                                      · rcases p512_3 (m.d 0 4) (by simp) with h549 | h549
                                        · linarith only [h549, h7, hlam]
                                        · rcases p512_3 (m.d 0 5) (by simp) with h551 | h551
                                          · linarith only [h551, h8, hlam]
                                          · linarith only [h551, h9, hlam]
                                      · linarith only [h548, h7, hlam]
                                    · linarith only [h5, h547, hlam]
                                  · linarith only [h2, h546, hlam]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  rcases p512_3 (m.d 0 1) (by simp) with h557 | h557
                                  · rcases p512_3 (m.d 0 2) (by simp) with h558 | h558
                                    · rcases p512_3 (m.d 0 3) (by simp) with h559 | h559
                                      · rcases p512_3 (m.d 0 4) (by simp) with h560 | h560
                                        · linarith only [h560, h7, hlam]
                                        · rcases p512_3 (m.d 0 5) (by simp) with h562 | h562
                                          · linarith only [h562, h8, hlam]
                                          · rcases h1bigk with h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              rcases p564_3 (m.d 0 1) (by simp) with h566 | h566
                                              · rcases p564_3 (m.d 1 2) (by simp) with h567 | h567
                                                · linarith only [h567, hlam, p564_0]
                                                · rcases p564_3 (m.d 1 3) (by simp) with h569 | h569
                                                  · linarith only [h1, h569, hlam]
                                                  · linarith only [h313, h569, hlam]
                                              · linarith only [h566, hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              rcases p564_3 (m.d 0 1) (by simp) with h573 | h573
                                              · rcases p564_3 (m.d 1 2) (by simp) with h574 | h574
                                                · linarith only [h0, h574, hlam]
                                                · rcases p564_3 (m.d 1 3) (by simp) with h576 | h576
                                                  · linarith only [h576, hlam, p564_0]
                                                  · rcases p564_3 (m.d 1 4) (by simp) with h578 | h578
                                                    · linarith only [h2, h578, hlam]
                                                    · rcases p564_3 (m.d 1 5) (by simp) with h580 | h580
                                                      · linarith only [h3, h580, hlam]
                                                      · rcases h3bigk with h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [hlam, p582_0]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          rcases p582_3 (m.d 0 3) (by simp) with h584 | h584
                                                          · rcases p582_3 (m.d 1 3) (by simp) with h585 | h585
                                                            · linarith only [h1, h585, hlam]
                                                            · rcases p582_3 (m.d 2 3) (by simp) with h587 | h587
                                                              · linarith only [h4, h587, hlam]
                                                              · linarith only [h313, h587, hlam]
                                                          · linarith only [h1, h584, hlam]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h0, h313, h4, h501, h506, h508, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p582_1]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h506, h508, h6, hlam, p512_1, p582_2]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h507, h6, hlam, p512_1, p582_2]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h1, hlam, p582_0]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [hlam, p582_0]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h313, hlam, p582_1]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p564_1, p582_1]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p564_1, p582_1]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h4, hlam, p582_0]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h0, h4, hlam, p564_2, p582_1]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [hlam, p582_0]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          rcases p582_3 (m.d 0 3) (by simp) with h602 | h602
                                                          · rcases p582_3 (m.d 1 3) (by simp) with h603 | h603
                                                            · linarith only [h313, h603, hlam]
                                                            · linarith only [h502, h603, hlam]
                                                          · linarith only [h602, h7, hlam]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          rcases p582_3 (m.d 0 3) (by simp) with h607 | h607
                                                          · rcases p582_3 (m.d 1 3) (by simp) with h608 | h608
                                                            · linarith only [h313, h608, hlam]
                                                            · linarith only [h503, h608, hlam]
                                                          · linarith only [h607, h8, hlam]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h7, hlam, p582_0]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h502, hlam, p582_0]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h506, hlam, p582_0]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [hlam, p582_0]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h510, hlam, p582_1]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h8, hlam, p582_0]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h503, hlam, p582_0]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h507, hlam, p582_0]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [h8, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p512_1, p582_1]
                                                        · have p582_0 := h582c.1
                                                          have p582_1 := h582c.2.1
                                                          have p582_2 := h582c.2.2.1
                                                          have p582_3 := h582c.2.2.2
                                                          linarith only [hlam, p582_0]
                                              · linarith only [h573, hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h0, h2, h4, h9, hlam, p512_1, p564_2]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h0, h3, h4, hlam, p512_1, p564_2]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h0, hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h313, hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h0, h313, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p564_1]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h0, h313, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p564_1]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h1, hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h0, h313, h4, h500, h506, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p564_1]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              rcases p564_3 (m.d 0 1) (by simp) with h633 | h633
                                              · rcases p564_3 (m.d 1 2) (by simp) with h634 | h634
                                                · linarith only [h313, h634, hlam]
                                                · linarith only [h500, h634, hlam]
                                              · linarith only [h2, h633, hlam]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              rcases p564_3 (m.d 0 1) (by simp) with h638 | h638
                                              · rcases p564_3 (m.d 1 2) (by simp) with h639 | h639
                                                · linarith only [h313, h639, hlam]
                                                · linarith only [h501, h639, hlam]
                                              · linarith only [h3, h638, hlam]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h2, hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h500, hlam, p564_1]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h502, hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h504, hlam, p564_1]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h3, hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h501, hlam, p564_1]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h503, hlam, p564_0]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [h0, h3, h4, h500, h506, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p512_1, p564_1]
                                            · have p564_0 := h564c.1
                                              have p564_1 := h564c.2.1
                                              have p564_2 := h564c.2.2.1
                                              have p564_3 := h564c.2.2.2
                                              linarith only [hlam, p564_0]
                                      · linarith only [h559, h8, hlam]
                                    · linarith only [h558, h6, hlam]
                                  · linarith only [h3, h557, hlam]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h2, hlam, p512_0]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h5, hlam, p512_0]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h7, hlam, p512_0]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [hlam, p512_0]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h9, hlam, p512_0]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h3, hlam, p512_0]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h6, hlam, p512_1]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h8, hlam, p512_0]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [h2, h500, h506, h9, hc34, hlam, hphi, p512_1, u4elo4]
                                · have p512_0 := h512c.1
                                  have p512_1 := h512c.2.1
                                  have p512_2 := h512c.2.2.1
                                  have p512_3 := h512c.2.2.2
                                  linarith only [hlam, p512_0]
                          · linarith only [h313, h501, h507, h8, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h313, h500, h506, hc24, hlam, hphi, u4elo3]
                    · linarith only [h313, h500, h503, h8, h9, hc24, hlam, hphi, u4elo4]
                  · linarith only [h313, h500, h502, hc24, hlam, hphi, u4elo3]
                · linarith only [h500, h501, h6, h9, hc24, hlam, hphi, u4elo4]
              · linarith only [h5, h500, h9, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h672 | h672
          · linarith only [h672, h7, h8, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h674 | h674
            · rcases m.htr 1 2 4 (by decide) (by decide) with h675 | h675
              · rcases m.htr 1 2 5 (by decide) (by decide) with h676 | h676
                · rcases m.htr 1 3 4 (by decide) (by decide) with h677 | h677
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h678 | h678
                    · linarith only [h1, h678, h8, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h680 | h680
                      · linarith only [h2, h672, h680, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h682 | h682
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h683 | h683
                          · linarith only [h1, h674, h683, h8, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h685 | h685
                            · linarith only [h2, h672, h675, h685, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h687 | h687
                              · linarith only [h1, h672, h674, h682, h687, h8, hlam]
                              · linarith only [h1, h674, h682, h687, h8, hc34, hlam, hphi, u4elo4]
                        · linarith only [h1, h677, h682, h8, hc23, hc35, hlam, hphi]
                  · linarith only [h672, h677, h7, h8, hc13, hlam, hphi, ht34, u4elo4]
                · linarith only [h6, h672, h674, h676, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h674, h675, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h694 | h694
              · linarith only [h4, h672, h674, h694, h8, hc24, hlam, hphi, u4elo4]
              · linarith only [h5, h672, h694, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h697 | h697
        · rcases m.htr 0 4 5 (by decide) (by decide) with h698 | h698
          · rcases m.htr 1 2 3 (by decide) (by decide) with h699 | h699
            · rcases m.htr 1 2 4 (by decide) (by decide) with h700 | h700
              · rcases m.htr 1 2 5 (by decide) (by decide) with h701 | h701
                · rcases m.htr 1 3 4 (by decide) (by decide) with h702 | h702
                  · linarith only [h1, h7, h702, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h704 | h704
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h705 | h705
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h706 | h706
                        · linarith only [h0, h1, h699, h7, h704, h706, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h708 | h708
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h709 | h709
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h710 | h710
                              · rcases h0bigk with h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [hlam, p711_0]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h4, h708, h710, hc01, hc45, hlam, hphi, ht0b, ht5b, p711_1]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h1, h699, h708, h710, hc01, hc45, hlam, hphi, ht0b, ht5b, p711_1]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h1, h699, h7, h708, h710, hc01, hc45, hlam, hphi, ht0b, ht5b, p711_1]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  rcases p711_3 (m.d 0 1) (by simp) with h716 | h716
                                  · rcases p711_3 (m.d 0 2) (by simp) with h717 | h717
                                    · linarith only [h0, h717, hlam]
                                    · linarith only [h6, h717, hlam]
                                  · linarith only [h3, h716, hlam]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h0, hlam, p711_0]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [hlam, p711_0]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h1, h699, h708, h710, hc02, hc45, hlam, hphi, ht0b, ht5b, p711_1]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h0, h1, h699, h7, h708, h710, hc01, hc45, hlam, hphi, ht0b, ht5b, p711_1]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  rcases p711_3 (m.d 0 1) (by simp) with h725 | h725
                                  · rcases p711_3 (m.d 0 2) (by simp) with h726 | h726
                                    · rcases p711_3 (m.d 0 3) (by simp) with h727 | h727
                                      · linarith only [h4, h727, hlam]
                                      · linarith only [h697, h727, hlam]
                                    · linarith only [h6, h726, hlam]
                                  · linarith only [h3, h725, hlam]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h1, hlam, p711_1]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h4, hlam, p711_1]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [hlam, p711_0]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h7, hlam, p711_1]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h7, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p711_1, u4elo3]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h2, hlam, p711_0]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h5, hlam, p711_0]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h1, h699, h708, hc04, hc35, hlam, hphi, ht0b, ht5b, p711_1]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [hlam, p711_0]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h3, h7, h701, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p711_1, u4elo3]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h3, hlam, p711_0]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h6, hlam, p711_1]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h697, hlam, p711_0]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [h698, hlam, p711_1]
                                · have p711_0 := h711c.1
                                  have p711_1 := h711c.2.1
                                  have p711_2 := h711c.2.2.1
                                  have p711_3 := h711c.2.2.2
                                  linarith only [hlam, p711_0]
                              · linarith only [h7, h710, hc03, hlam, hphi, ht34, u4elo4]
                            · linarith only [h3, h697, h7, h705, h709, hc24, hlam, hphi, u4elo3]
                          · linarith only [h697, h7, h708, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h698, h7, h705, hc14, hlam, hphi, u4elo3]
                    · linarith only [h697, h7, h704, hc13, hlam, hphi, ht34, u4elo3]
                · linarith only [h6, h697, h7, h701, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h699, h700, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h4, h699, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h697, h698, h7, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h756 | h756
          · rcases m.htr 1 2 3 (by decide) (by decide) with h757 | h757
            · rcases m.htr 1 2 4 (by decide) (by decide) with h758 | h758
              · rcases m.htr 1 2 5 (by decide) (by decide) with h759 | h759
                · rcases m.htr 1 3 4 (by decide) (by decide) with h760 | h760
                  · linarith only [h1, h7, h760, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h762 | h762
                    · linarith only [h697, h760, h762, hc03, hlam, hphi, ht34, u4elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h764 | h764
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h765 | h765
                        · linarith only [h1, h7, h757, h765, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h767 | h767
                          · linarith only [h1, h697, h757, h767, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h769 | h769
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h770 | h770
                              · rcases h0bigk with h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [hlam, p771_0]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h0, h758, h769, hc01, hc45, hlam, hphi, ht0b, ht5b, p771_1]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  rcases p771_3 (m.d 0 1) (by simp) with h774 | h774
                                  · rcases p771_3 (m.d 0 2) (by simp) with h775 | h775
                                    · linarith only [h0, h775, hlam]
                                    · linarith only [h4, h775, hlam]
                                  · linarith only [h1, h774, hlam]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h2, h758, h769, hc01, hc45, hlam, hphi, ht0b, ht5b, p771_1]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  rcases p771_3 (m.d 0 1) (by simp) with h780 | h780
                                  · rcases p771_3 (m.d 0 2) (by simp) with h781 | h781
                                    · linarith only [h0, h781, hlam]
                                    · linarith only [h6, h781, hlam]
                                  · linarith only [h3, h780, hlam]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h0, hlam, p771_0]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [hlam, p771_0]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  rcases p771_3 (m.d 0 1) (by simp) with h787 | h787
                                  · rcases p771_3 (m.d 0 2) (by simp) with h788 | h788
                                    · rcases p771_3 (m.d 0 3) (by simp) with h789 | h789
                                      · linarith only [h4, h789, hlam]
                                      · rcases p771_3 (m.d 0 4) (by simp) with h791 | h791
                                        · linarith only [h5, h791, hlam]
                                        · linarith only [h7, h791, hlam]
                                    · linarith only [h4, h788, hlam]
                                  · linarith only [h1, h787, hlam]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h2, h758, h769, hc02, hc45, hlam, hphi, ht0b, ht5b, p771_1]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  rcases p771_3 (m.d 0 1) (by simp) with h797 | h797
                                  · rcases p771_3 (m.d 0 2) (by simp) with h798 | h798
                                    · rcases p771_3 (m.d 0 3) (by simp) with h799 | h799
                                      · linarith only [h4, h799, hlam]
                                      · rcases p771_3 (m.d 0 4) (by simp) with h801 | h801
                                        · linarith only [h5, h801, hlam]
                                        · linarith only [h756, h801, hlam]
                                    · linarith only [h6, h798, hlam]
                                  · linarith only [h3, h797, hlam]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h1, hlam, p771_1]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h4, hlam, p771_1]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [hlam, p771_0]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h7, hlam, p771_1]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h697, hlam, p771_1]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h2, hlam, p771_0]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h5, hlam, p771_0]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h1, h757, hc23, hlam, hphi, ht34, p771_1, u4elo0]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [hlam, p771_0]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h1, h697, h7, h757, hc23, hlam, hphi, ht34, p771_1, u4elo3]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h3, hlam, p771_0]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h6, hlam, p771_1]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h1, h697, h757, hc23, hc35, hlam, hphi, p771_1]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [h756, hlam, p771_1]
                                · have p771_0 := h771c.1
                                  have p771_1 := h771c.2.1
                                  have p771_2 := h771c.2.2.1
                                  have p771_3 := h771c.2.2.2
                                  linarith only [hlam, p771_0]
                              · linarith only [h7, h758, h769, h770, hc04, hlam, hphi, u4elo1]
                            · linarith only [h2, h7, h764, h769, hc24, hlam, hphi, u4elo3]
                      · linarith only [h7, h756, h764, hc14, hlam, hphi, u4elo3]
                · linarith only [h6, h7, h756, h757, h759, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h757, h758, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h4, h7, h757, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h827 | h827
            · rcases m.htr 1 2 4 (by decide) (by decide) with h828 | h828
              · rcases m.htr 1 2 5 (by decide) (by decide) with h829 | h829
                · rcases m.htr 1 3 4 (by decide) (by decide) with h830 | h830
                  · linarith only [h1, h7, h756, h830, hc34, hlam, hphi, u4elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h832 | h832
                    · linarith only [h1, h697, h832, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h834 | h834
                      · linarith only [h2, h756, h834, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h836 | h836
                        · linarith only [h1, h7, h827, h836, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h838 | h838
                          · linarith only [h1, h697, h827, h838, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h840 | h840
                            · linarith only [h756, h840, hc04, hlam, hphi, u4elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h842 | h842
                              · linarith only [h1, h7, h756, h827, h842, hc23, hlam, hphi, ht34, u4elo3]
                              · linarith only [h1, h7, h827, h842, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h6, h756, h827, h829, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h827, h828, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h4, h7, h827, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h848 | h848
      · rcases m.htr 0 3 5 (by decide) (by decide) with h849 | h849
        · linarith only [h4, h6, h849, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h851 | h851
          · linarith only [h5, h6, h851, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h853 | h853
            · rcases m.htr 1 2 4 (by decide) (by decide) with h854 | h854
              · rcases m.htr 1 2 5 (by decide) (by decide) with h855 | h855
                · linarith only [h0, h6, h855, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h857 | h857
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h858 | h858
                    · linarith only [h1, h849, h858, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h860 | h860
                      · linarith only [h2, h851, h860, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h862 | h862
                        · linarith only [h4, h6, h851, h862, hc34, hlam, hphi, u4elo4]
                        · linarith only [h1, h849, h857, h862, hc23, hc35, hlam, hphi]
                  · linarith only [h4, h6, h848, h851, h857, hc13, hlam, hphi, ht34, u4elo4]
              · linarith only [h5, h6, h851, h854, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · linarith only [h4, h6, h851, h853, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h868 | h868
        · linarith only [h4, h6, h868, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h870 | h870
          · linarith only [h5, h6, h870, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h872 | h872
            · rcases m.htr 1 2 4 (by decide) (by decide) with h873 | h873
              · rcases m.htr 1 2 5 (by decide) (by decide) with h874 | h874
                · linarith only [h0, h6, h874, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h876 | h876
                  · linarith only [h1, h848, h870, h876, hc34, hlam, hphi, u4elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h878 | h878
                    · linarith only [h1, h868, h878, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h880 | h880
                      · linarith only [h2, h870, h880, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h882 | h882
                        · linarith only [h0, h1, h6, h848, h872, h882, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h884 | h884
                          · linarith only [h1, h6, h848, h868, h872, h884, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h886 | h886
                            · linarith only [h0, h6, h848, h870, h873, h886, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · linarith only [h0, h6, h873, h882, h886, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h872, h873, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h4, h6, h872, hc12, hc25, hlam, hphi]
  · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]

end R2N4
