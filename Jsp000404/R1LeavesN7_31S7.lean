import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
  · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
      · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
        · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
          · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
            · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                · linarith only [h0, h13, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h10, h13, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                · linarith only [h0, h16, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h10, h16, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
              · linarith only [h10, h11, h19, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                · linarith only [h0, h21, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h10, h11, h19, h21, h4, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
            · linarith only [h1, h10, h24, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
              · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                · linarith only [h0, h10, h27, h7, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                  · linarith only [h0, h29, h8, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h2, h26, h29, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                · linarith only [h0, h32, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                  · linarith only [h0, h10, h26, h34, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                    · linarith only [h1, h10, h26, h36, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h0, h10, h36, h4, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h39 | h39
          · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
            · linarith only [h40, h7, h9, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
              · linarith only [h42, h8, h9, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                · linarith only [h0, h4, h42, h44, h6, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h39, h4, h42, h44, h6, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
            · linarith only [h1, h39, h47, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
              · linarith only [h49, h8, h9, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                · linarith only [h0, h51, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                  · linarith only [h0, h39, h4, h49, h53, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h4, h51, h53, h6, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · linarith only [h0, h4, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
      · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
        · rcases m.htr 1 3 4 (by decide) (by decide) with h59 | h59
          · rcases m.htr 1 3 5 (by decide) (by decide) with h60 | h60
            · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
              · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                  · linarith only [h0, h57, h63, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h1, h57, h61, h63, h7, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h1, h5, h58, h62, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                  · linarith only [h57, h61, h68, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h70 | h70
                    · linarith only [h57, h61, h67, h70, hlam]
                    · rcases h1bigk with h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h57, h67, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p72_1, u1elo0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h60, hc35, hlam, hphi, ht01, ht0b, ht5b, p72_1, u1elo0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        rcases p72_3 (m.d 0 1) (by simp) with h76 | h76
                        · rcases p72_3 (m.d 1 2) (by simp) with h77 | h77
                          · linarith only [h0, h77, hlam]
                          · linarith only [h57, h77, hlam]
                        · linarith only [h76, hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        rcases p72_3 (m.d 0 1) (by simp) with h81 | h81
                        · rcases p72_3 (m.d 1 2) (by simp) with h82 | h82
                          · linarith only [h0, h82, hlam]
                          · linarith only [h58, h82, hlam]
                        · linarith only [h81, hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h0, hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h7, hlam, p72_1]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h0, h57, h67, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p72_1, u1elo0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h1, h7, hc15, hlam, hphi, ht01, ht0b, ht5b, p72_1, u1elo0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h1, hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p72_1, u1elo0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h1, h57, h67, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p72_1, u1elo0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h1, h58, h67, h68, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p72_1, u1elo0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h2, hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h57, hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h59, hlam, p72_1]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h61, hlam, p72_1]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h3, hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h58, hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h60, hlam, p72_0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [h3, h57, h67, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p72_1, u1elo0]
                      · have p72_0 := h72c.1
                        have p72_1 := h72c.2.1
                        have p72_2 := h72c.2.2.1
                        have p72_3 := h72c.2.2.2
                        linarith only [hlam, p72_0]
                · linarith only [h1, h5, h67, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h58, h60, h7, hlam]
          · linarith only [h1, h5, h57, h59, h7, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h109 | h109
          · rcases m.htr 1 3 5 (by decide) (by decide) with h110 | h110
            · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
              · linarith only [h111, h57, h58, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
                  · linarith only [h111, h114, h57, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h113, h114, h4, h57, h58, h6, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h1, h113, h5, h57, h7, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
              · linarith only [h110, h118, h57, h7, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                  · linarith only [h110, h118, h121, h57, h7, hlam]
                  · linarith only [h0, h121, h4, h57, h58, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h1, h120, h5, h57, h7, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · linarith only [h1, h109, h5, h57, h7, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
        · linarith only [h0, h126, h4, h57, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
          · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
            · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
              · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
                · rcases m.htr 2 4 5 (by decide) (by decide) with h132 | h132
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h133 | h133
                    · linarith only [h1, h128, h133, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h130, h133, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h130, h132, h57, hlam]
                · linarith only [h1, h131, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                · rcases m.htr 2 4 5 (by decide) (by decide) with h139 | h139
                  · linarith only [h0, h130, h139, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h139, h4, h57, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h1, h129, h138, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h143 | h143
              · linarith only [h128, h129, h143, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
                · rcases m.htr 2 4 5 (by decide) (by decide) with h146 | h146
                  · linarith only [h0, h143, h146, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h146, h4, h57, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h128, h145, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h150 | h150
            · linarith only [h1, h128, h150, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
              · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h155 | h155
                    · rcases h1bigk with h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        rcases p156_3 (m.d 0 1) (by simp) with h158 | h158
                        · rcases p156_3 (m.d 1 2) (by simp) with h159 | h159
                          · linarith only [h159, hlam, p156_0]
                          · rcases p156_3 (m.d 1 3) (by simp) with h161 | h161
                            · linarith only [h1, h161, hlam]
                            · linarith only [h161, h7, hlam]
                        · linarith only [h158, hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        rcases p156_3 (m.d 0 1) (by simp) with h165 | h165
                        · rcases p156_3 (m.d 1 2) (by simp) with h166 | h166
                          · linarith only [h0, h166, hlam]
                          · rcases p156_3 (m.d 1 3) (by simp) with h168 | h168
                            · linarith only [h168, hlam, p156_0]
                            · rcases p156_3 (m.d 1 4) (by simp) with h170 | h170
                              · linarith only [h170, h2, hlam]
                              · linarith only [h128, h170, hlam]
                        · linarith only [h165, hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h152, hc45, hlam, hphi, ht01, ht0b, ht5b, p156_1, u1elo0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        rcases p156_3 (m.d 0 1) (by simp) with h175 | h175
                        · rcases p156_3 (m.d 1 2) (by simp) with h176 | h176
                          · linarith only [h0, h176, hlam]
                          · rcases p156_3 (m.d 1 3) (by simp) with h178 | h178
                            · linarith only [h1, h178, hlam]
                            · rcases p156_3 (m.d 1 4) (by simp) with h180 | h180
                              · linarith only [h180, h2, hlam]
                              · linarith only [h152, h180, hlam]
                        · linarith only [h175, hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h0, hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h7, hlam, p156_1]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h57, hlam, p156_1]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h126, hlam, p156_1]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h1, hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h0, h150, h153, h155, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p156_1, u1elo0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h128, hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h150, hlam, p156_1]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h2, hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p156_1, u1elo0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h0, h128, h153, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p156_1, u1elo0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h0, h128, h153, h4, hc15, hlam, hphi, ht01, ht0b, ht5b, p156_1, u1elo0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h3, hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p156_1, u1elo0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h0, h150, h153, h155, h4, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p156_1, u1elo0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [h152, hlam, p156_0]
                      · have p156_0 := h156c.1
                        have p156_1 := h156c.2.1
                        have p156_2 := h156c.2.2.1
                        have p156_3 := h156c.2.2.2
                        linarith only [hlam, p156_0]
                    · linarith only [h0, h128, h155, h4, h6, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h152, h154, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h1, h153, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                · rcases m.htr 2 4 5 (by decide) (by decide) with h208 | h208
                  · linarith only [h0, h128, h152, h208, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h208, h4, h57, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h1, h207, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h212 | h212
    · rcases m.htr 1 2 4 (by decide) (by decide) with h213 | h213
      · rcases m.htr 1 2 5 (by decide) (by decide) with h214 | h214
        · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
          · rcases m.htr 1 3 5 (by decide) (by decide) with h216 | h216
            · rcases m.htr 1 4 5 (by decide) (by decide) with h217 | h217
              · linarith only [h2, h217, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h219 | h219
                · linarith only [h0, h212, h219, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h1, h215, h219, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h222 | h222
              · linarith only [h2, h215, h216, h222, h3, h6, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                · linarith only [h0, h212, h224, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h214, h215, h216, h224, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
            · linarith only [h1, h215, h227, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h229 | h229
              · linarith only [h1, h215, h229, h5, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
                · linarith only [h212, h215, h231, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h233 | h233
                  · linarith only [h0, h212, h215, h233, h4, h5, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h235 | h235
                    · linarith only [h235, h5, h6, hlam]
                    · rcases h1bigk with h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h214, h233, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p237_1, u1elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        rcases p237_3 (m.d 0 1) (by simp) with h240 | h240
                        · rcases p237_3 (m.d 1 2) (by simp) with h241 | h241
                          · linarith only [h0, h241, hlam]
                          · linarith only [h212, h241, hlam]
                        · linarith only [h240, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        rcases p237_3 (m.d 0 1) (by simp) with h245 | h245
                        · rcases p237_3 (m.d 1 2) (by simp) with h246 | h246
                          · linarith only [h0, h246, hlam]
                          · linarith only [h213, h246, hlam]
                        · linarith only [h245, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        rcases p237_3 (m.d 0 1) (by simp) with h250 | h250
                        · rcases p237_3 (m.d 1 2) (by simp) with h251 | h251
                          · linarith only [h0, h251, hlam]
                          · linarith only [h214, h251, hlam]
                        · linarith only [h250, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h0, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h0, h212, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p237_1, u1elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h0, h212, h215, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p237_1, u1elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p237_1, u1elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h1, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h212, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h215, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h227, hlam, p237_1]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h2, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h213, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h2, h212, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p237_1, u1elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h229, hlam, p237_1]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h3, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h214, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h212, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p237_1, u1elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h0, h214, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p237_1, u1elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [hlam, p237_0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h275 | h275
          · rcases m.htr 1 3 5 (by decide) (by decide) with h276 | h276
            · linarith only [h212, h214, h276, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
              · linarith only [h2, h278, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
                · linarith only [h212, h214, h280, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h212, h214, h275, h280, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h283 | h283
            · linarith only [h1, h275, h283, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h285 | h285
              · linarith only [h2, h285, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h287 | h287
                · linarith only [h212, h275, h287, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h289 | h289
                  · linarith only [h0, h212, h275, h289, h4, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h291 | h291
                    · linarith only [h1, h214, h289, h291, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases h1bigk with h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h213, h287, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p293_1, u1elo0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        rcases p293_3 (m.d 0 1) (by simp) with h296 | h296
                        · rcases p293_3 (m.d 1 2) (by simp) with h297 | h297
                          · linarith only [h0, h297, hlam]
                          · linarith only [h212, h297, hlam]
                        · linarith only [h296, hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        rcases p293_3 (m.d 0 1) (by simp) with h301 | h301
                        · rcases p293_3 (m.d 1 2) (by simp) with h302 | h302
                          · linarith only [h0, h302, hlam]
                          · linarith only [h213, h302, hlam]
                        · linarith only [h301, hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h213, h214, h287, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p293_1, u1elo0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h0, hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h0, h212, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p293_1, u1elo0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h212, h214, h275, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p293_1, u1elo0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h214, hlam, p293_1]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h1, hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h212, hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h275, hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h283, hlam, p293_1]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h2, hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h213, hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h2, h212, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p293_1, u1elo0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h285, hlam, p293_1]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h3, hlam, p293_0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p293_1, u1elo0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h212, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p293_1, u1elo0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p293_1, u1elo0]
                      · have p293_0 := h293c.1
                        have p293_1 := h293c.2.1
                        have p293_2 := h293c.2.2.1
                        have p293_3 := h293c.2.2.2
                        linarith only [hlam, p293_0]
      · linarith only [h0, h212, h213, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
      · rcases m.htr 1 2 5 (by decide) (by decide) with h329 | h329
        · rcases m.htr 1 3 4 (by decide) (by decide) with h330 | h330
          · rcases m.htr 1 3 5 (by decide) (by decide) with h331 | h331
            · rcases m.htr 1 4 5 (by decide) (by decide) with h332 | h332
              · linarith only [h2, h332, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h334 | h334
                · rcases m.htr 2 4 5 (by decide) (by decide) with h335 | h335
                  · linarith only [h2, h328, h335, h6, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h337 | h337
                    · linarith only [h2, h328, h334, h337, h6, hlam]
                    · rcases h1bigk with h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h329, h334, h335, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p339_1, u1elo0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h212, h329, h334, h335, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p339_1, u1elo0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        rcases p339_3 (m.d 0 1) (by simp) with h343 | h343
                        · rcases p339_3 (m.d 1 2) (by simp) with h344 | h344
                          · linarith only [h0, h344, hlam]
                          · linarith only [h328, h344, hlam]
                        · linarith only [h343, hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        rcases p339_3 (m.d 0 1) (by simp) with h348 | h348
                        · rcases p339_3 (m.d 1 2) (by simp) with h349 | h349
                          · linarith only [h0, h349, hlam]
                          · linarith only [h329, h349, hlam]
                        · linarith only [h348, hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h0, hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h212, hlam, p339_1]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h0, h328, h334, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p339_1, u1elo0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h1, h212, hc15, hlam, hphi, ht01, ht0b, ht5b, p339_1, u1elo0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h1, hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p339_1, u1elo0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h1, h328, h334, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p339_1, u1elo0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h1, h329, h334, h335, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p339_1, u1elo0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h2, hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h328, hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h330, hlam, p339_1]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h332, hlam, p339_1]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h3, hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h329, hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h331, hlam, p339_0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [h3, h328, h334, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p339_1, u1elo0]
                      · have p339_0 := h339c.1
                        have p339_1 := h339c.2.1
                        have p339_2 := h339c.2.2.1
                        have p339_3 := h339c.2.2.2
                        linarith only [hlam, p339_0]
                · linarith only [h1, h212, h334, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · linarith only [h212, h329, h331, hlam]
          · linarith only [h1, h212, h328, h330, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h376 | h376
          · rcases m.htr 1 3 5 (by decide) (by decide) with h377 | h377
            · rcases m.htr 1 4 5 (by decide) (by decide) with h378 | h378
              · linarith only [h2, h3, h328, h329, h378, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
                · rcases m.htr 2 4 5 (by decide) (by decide) with h381 | h381
                  · linarith only [h328, h381, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h383 | h383
                    · linarith only [h328, h329, h380, h381, h383, hlam]
                    · rcases h1bigk with h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [hlam, p385_0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h328, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p385_1, u1elo0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h377, hc35, hlam, hphi, ht01, ht0b, ht5b, p385_1, u1elo0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        rcases p385_3 (m.d 0 1) (by simp) with h389 | h389
                        · rcases p385_3 (m.d 1 2) (by simp) with h390 | h390
                          · linarith only [h0, h390, hlam]
                          · linarith only [h328, h390, hlam]
                        · linarith only [h389, hlam, p385_0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h328, h329, h380, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p385_1, u1elo0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h0, hlam, p385_0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [hlam, p385_0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h212, hlam, p385_1]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h328, h329, h380, h381, hc34, hc45, hlam, hphi, p385_1]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h329, hlam, p385_1]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h1, hlam, p385_0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p385_1, u1elo0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [hlam, p385_0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h1, h328, h380, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p385_1, u1elo0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p385_1, u1elo0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h2, hlam, p385_0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h328, hlam, p385_0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h376, hlam, p385_1]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [hlam, p385_0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h378, hlam, p385_1]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h3, hlam, p385_0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h328, h380, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p385_1, u1elo4]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h377, hlam, p385_0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [h1, h328, h377, h380, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p385_1, u1elo0]
                      · have p385_0 := h385c.1
                        have p385_1 := h385c.2.1
                        have p385_2 := h385c.2.2.1
                        have p385_3 := h385c.2.2.2
                        linarith only [hlam, p385_0]
                · linarith only [h1, h212, h380, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h416 | h416
              · linarith only [h2, h416, h6, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h418 | h418
                · rcases m.htr 2 4 5 (by decide) (by decide) with h419 | h419
                  · linarith only [h328, h419, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h421 | h421
                    · linarith only [h328, h329, h418, h419, h421, hlam]
                    · rcases h1bigk with h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h328, h418, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p423_1, u1elo0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h212, h328, h418, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p423_1, u1elo0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        rcases p423_3 (m.d 0 1) (by simp) with h427 | h427
                        · rcases p423_3 (m.d 1 2) (by simp) with h428 | h428
                          · linarith only [h0, h428, hlam]
                          · linarith only [h328, h428, hlam]
                        · linarith only [h427, hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h328, h329, h418, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p423_1, u1elo0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h0, hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h212, hlam, p423_1]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h212, h328, h377, h418, h421, hc34, hc45, hlam, hphi, p423_1]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h329, hlam, p423_1]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h1, hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h377, hc12, hc35, hlam, hphi, ht23, p423_1]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h1, h328, h418, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p423_1, u1elo0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h377, hlam, p423_1]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h2, hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h328, hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h376, hlam, p423_1]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h416, hlam, p423_1]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h3, hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h328, h418, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p423_1, u1elo4]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p423_1, u1elo0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h3, h328, h418, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p423_1, u1elo0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hlam, p423_0]
                · linarith only [h1, h212, h328, h418, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · linarith only [h1, h212, h328, h376, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h455 | h455
        · linarith only [h0, h328, h4, h455, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h457 | h457
          · rcases m.htr 1 3 5 (by decide) (by decide) with h458 | h458
            · rcases m.htr 1 4 5 (by decide) (by decide) with h459 | h459
              · linarith only [h328, h4, h459, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h461 | h461
                · rcases m.htr 2 4 5 (by decide) (by decide) with h462 | h462
                  · linarith only [h4, h462, h6, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h464 | h464
                    · linarith only [h328, h4, h464, h6, hc12, hc34, hlam, hphi, ht23]
                    · rcases h1bigk with h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [hlam, p466_0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        rcases p466_3 (m.d 0 1) (by simp) with h468 | h468
                        · rcases p466_3 (m.d 1 2) (by simp) with h469 | h469
                          · linarith only [h469, hlam, p466_0]
                          · rcases p466_3 (m.d 1 3) (by simp) with h471 | h471
                            · linarith only [h1, h471, hlam]
                            · linarith only [h212, h471, hlam]
                        · linarith only [h468, hlam, p466_0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h458, h464, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p466_1, u1elo0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        rcases p466_3 (m.d 0 1) (by simp) with h476 | h476
                        · rcases p466_3 (m.d 1 2) (by simp) with h477 | h477
                          · linarith only [h0, h477, hlam]
                          · rcases p466_3 (m.d 1 3) (by simp) with h479 | h479
                            · linarith only [h1, h479, hlam]
                            · linarith only [h457, h479, hlam]
                        · linarith only [h476, hlam, p466_0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        rcases p466_3 (m.d 0 1) (by simp) with h483 | h483
                        · rcases p466_3 (m.d 1 2) (by simp) with h484 | h484
                          · linarith only [h0, h484, hlam]
                          · rcases p466_3 (m.d 1 3) (by simp) with h486 | h486
                            · linarith only [h1, h486, hlam]
                            · linarith only [h458, h486, hlam]
                        · linarith only [h483, hlam, p466_0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h0, hlam, p466_0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [hlam, p466_0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h212, hlam, p466_1]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h328, hlam, p466_1]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h455, hlam, p466_1]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h1, hlam, p466_0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p466_1, u1elo0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [hlam, p466_0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h1, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p466_1, u1elo0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p466_1, u1elo0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h2, hlam, p466_0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p466_1, u1elo0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h457, hlam, p466_1]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [hlam, p466_0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h459, hlam, p466_1]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h3, hlam, p466_0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p466_1, u1elo0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h458, hlam, p466_0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [h1, h458, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p466_1, u1elo0]
                      · have p466_0 := h466c.1
                        have p466_1 := h466c.2.1
                        have p466_2 := h466c.2.2.1
                        have p466_3 := h466c.2.2.2
                        linarith only [hlam, p466_0]
                · linarith only [h1, h212, h461, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h511 | h511
              · linarith only [h2, h511, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h513 | h513
                · rcases m.htr 2 4 5 (by decide) (by decide) with h514 | h514
                  · linarith only [h4, h514, h6, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h516 | h516
                    · linarith only [h328, h4, h457, h516, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases h1bigk with h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [hlam, p518_0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        rcases p518_3 (m.d 0 1) (by simp) with h520 | h520
                        · rcases p518_3 (m.d 1 2) (by simp) with h521 | h521
                          · linarith only [h521, hlam, p518_0]
                          · rcases p518_3 (m.d 1 3) (by simp) with h523 | h523
                            · linarith only [h1, h523, hlam]
                            · linarith only [h212, h523, hlam]
                        · linarith only [h520, hlam, p518_0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h457, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p518_1, u1elo0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        rcases p518_3 (m.d 0 1) (by simp) with h528 | h528
                        · rcases p518_3 (m.d 1 2) (by simp) with h529 | h529
                          · linarith only [h0, h529, hlam]
                          · rcases p518_3 (m.d 1 3) (by simp) with h531 | h531
                            · linarith only [h1, h531, hlam]
                            · linarith only [h457, h531, hlam]
                        · linarith only [h528, hlam, p518_0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h457, h458, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p518_1, u1elo0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h0, hlam, p518_0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [hlam, p518_0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h212, hlam, p518_1]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h328, hlam, p518_1]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h455, hlam, p518_1]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h1, hlam, p518_0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p518_1, u1elo0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [hlam, p518_0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h1, h328, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p518_1, u1elo0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h458, hlam, p518_1]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h2, hlam, p518_0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p518_1, u1elo0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h457, hlam, p518_1]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [hlam, p518_0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h511, hlam, p518_1]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h3, hlam, p518_0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p518_1, u1elo0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p518_1, u1elo0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p518_1, u1elo0]
                      · have p518_0 := h518c.1
                        have p518_1 := h518c.2.1
                        have p518_2 := h518c.2.2.1
                        have p518_3 := h518c.2.2.2
                        linarith only [hlam, p518_0]
                · linarith only [h212, h457, h513, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h557 | h557
            · linarith only [h1, h457, h5, h557, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h559 | h559
              · linarith only [h2, h559, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h561 | h561
                · rcases m.htr 2 4 5 (by decide) (by decide) with h562 | h562
                  · linarith only [h4, h562, h6, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h564 | h564
                    · linarith only [h4, h561, h564, h6, hlam]
                    · rcases h1bigk with h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [hlam, p566_0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        rcases p566_3 (m.d 0 1) (by simp) with h568 | h568
                        · rcases p566_3 (m.d 1 2) (by simp) with h569 | h569
                          · linarith only [h569, hlam, p566_0]
                          · rcases p566_3 (m.d 1 3) (by simp) with h571 | h571
                            · linarith only [h1, h571, hlam]
                            · linarith only [h212, h571, hlam]
                        · linarith only [h568, hlam, p566_0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        rcases p566_3 (m.d 0 1) (by simp) with h575 | h575
                        · rcases p566_3 (m.d 1 2) (by simp) with h576 | h576
                          · linarith only [h0, h576, hlam]
                          · rcases p566_3 (m.d 1 3) (by simp) with h578 | h578
                            · linarith only [h578, hlam, p566_0]
                            · rcases p566_3 (m.d 1 4) (by simp) with h580 | h580
                              · linarith only [h2, h580, hlam]
                              · linarith only [h457, h580, hlam]
                        · linarith only [h575, hlam, p566_0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        rcases p566_3 (m.d 0 1) (by simp) with h584 | h584
                        · rcases p566_3 (m.d 1 2) (by simp) with h585 | h585
                          · linarith only [h0, h585, hlam]
                          · rcases p566_3 (m.d 1 3) (by simp) with h587 | h587
                            · linarith only [h1, h587, hlam]
                            · rcases p566_3 (m.d 1 4) (by simp) with h589 | h589
                              · linarith only [h589, hlam, p566_0]
                              · rcases p566_3 (m.d 1 5) (by simp) with h591 | h591
                                · linarith only [h3, h591, hlam]
                                · linarith only [h559, h591, hlam]
                        · linarith only [h584, hlam, p566_0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        rcases p566_3 (m.d 0 1) (by simp) with h595 | h595
                        · rcases p566_3 (m.d 1 2) (by simp) with h596 | h596
                          · linarith only [h0, h596, hlam]
                          · rcases p566_3 (m.d 1 3) (by simp) with h598 | h598
                            · linarith only [h1, h598, hlam]
                            · rcases p566_3 (m.d 1 4) (by simp) with h600 | h600
                              · linarith only [h2, h600, hlam]
                              · rcases p566_3 (m.d 1 5) (by simp) with h602 | h602
                                · linarith only [h602, hlam, p566_0]
                                · rcases h4bigk with h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h212, h457, h6, hc12, hc45, hlam, hphi, ht23, ht34, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h212, h457, h561, h6, hc12, hc45, hlam, hphi, ht23, ht34, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h212, h457, h6, hc12, hc45, hlam, hphi, ht23, ht34, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h6, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h2, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h328, hlam, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h457, hlam, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h559, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h4, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h0, h212, h4, h457, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p604_1, u1elo0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h0, h212, h4, h457, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p604_1, u1elo0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h562, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h5, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h212, h457, h561, hc12, hc23, hlam, hphi, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h561, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h564, hlam, p604_0]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h328, h4, hc12, hc45, hlam, hphi, ht23, ht34, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    rcases p604_3 (m.d 0 4) (by simp) with h626 | h626
                                    · linarith only [h6, h626, hlam]
                                    · linarith only [h2, h626, hlam]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h212, h457, h561, hc12, hc45, hlam, hphi, ht23, ht34, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [h212, h457, hc12, hc45, hlam, hphi, ht23, ht34, p604_1]
                                  · have p604_0 := h604c.1
                                    have p604_1 := h604c.2.1
                                    have p604_2 := h604c.2.2.1
                                    have p604_3 := h604c.2.2.2
                                    linarith only [hlam, p604_0]
                        · linarith only [h595, hlam, p566_0]
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
                        linarith only [h212, hlam, p566_1]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h328, hlam, p566_1]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h455, hlam, p566_1]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h1, hlam, p566_0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h457, h561, hc12, hc24, hlam, hphi, p566_1]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [hlam, p566_0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h457, hlam, p566_0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h557, hlam, p566_1]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h2, hlam, p566_0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h0, h328, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p566_1, u1elo0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h0, h328, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p566_1, u1elo0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [hlam, p566_0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h559, hlam, p566_1]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h3, hlam, p566_0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p566_1, u1elo0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h212, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p566_1, u1elo0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p566_1, u1elo0]
                      · have p566_0 := h566c.1
                        have p566_1 := h566c.2.1
                        have p566_2 := h566c.2.2.1
                        have p566_3 := h566c.2.2.2
                        linarith only [hlam, p566_0]
                · linarith only [h1, h212, h5, h561, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]

end R2N4
