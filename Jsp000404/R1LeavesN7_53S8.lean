import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
  · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
    · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
      · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
        · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
          · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
            · linarith only [h0, h14, h17, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h14, h16, h17, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
            · linarith only [h0, h11, h16, h20, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
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
                linarith only [h0, h15, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p22_1]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                rcases p22_3 (m.d 0 2) (by simp) with h25 | h25
                · rcases p22_3 (m.d 1 2) (by simp) with h26 | h26
                  · linarith only [h0, h26, hlam]
                  · linarith only [h26, h8, hlam]
                · linarith only [h25, hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                rcases p22_3 (m.d 0 2) (by simp) with h30 | h30
                · rcases p22_3 (m.d 1 2) (by simp) with h31 | h31
                  · linarith only [h0, h31, hlam]
                  · linarith only [h31, h9, hlam]
                · linarith only [h30, hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                rcases p22_3 (m.d 0 2) (by simp) with h35 | h35
                · rcases p22_3 (m.d 1 2) (by simp) with h36 | h36
                  · linarith only [h0, h36, hlam]
                  · linarith only [h10, h36, hlam]
                · linarith only [h35, hlam, p22_0]
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
                linarith only [h0, h15, h20, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                rcases p22_3 (m.d 0 2) (by simp) with h43 | h43
                · rcases p22_3 (m.d 1 2) (by simp) with h44 | h44
                  · rcases p22_3 (m.d 2 3) (by simp) with h45 | h45
                    · linarith only [h45, h8, hlam]
                    · linarith only [h14, h45, hlam]
                  · linarith only [h44, hlam, p22_0]
                · linarith only [h4, h43, hlam]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                rcases p22_3 (m.d 0 2) (by simp) with h50 | h50
                · rcases p22_3 (m.d 1 2) (by simp) with h51 | h51
                  · rcases p22_3 (m.d 2 3) (by simp) with h52 | h52
                    · linarith only [h52, h8, hlam]
                    · linarith only [h15, h52, hlam]
                  · linarith only [h51, hlam, p22_0]
                · linarith only [h5, h50, hlam]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h3, hlam, p22_0]
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
                linarith only [h0, h14, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h0, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p22_1]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h4, hlam, p22_0]
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
                linarith only [h5, hlam, p22_0]
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
                linarith only [h0, h10, h14, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [hlam, p22_0]
        · linarith only [h0, h12, h14, h15, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
        · linarith only [h0, h11, h14, h73, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
          · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
            · rcases h2bigk with h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h11, h14, h75, h8, hc02, hc45, hlam, hphi, ht0b, ht5b, p77_1]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                rcases p77_3 (m.d 0 2) (by simp) with h80 | h80
                · rcases p77_3 (m.d 1 2) (by simp) with h81 | h81
                  · linarith only [h0, h81, hlam]
                  · linarith only [h8, h81, hlam]
                · linarith only [h80, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                rcases p77_3 (m.d 0 2) (by simp) with h85 | h85
                · rcases p77_3 (m.d 1 2) (by simp) with h86 | h86
                  · linarith only [h0, h86, hlam]
                  · linarith only [h86, h9, hlam]
                · linarith only [h85, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                rcases p77_3 (m.d 0 2) (by simp) with h90 | h90
                · rcases p77_3 (m.d 1 2) (by simp) with h91 | h91
                  · linarith only [h0, h91, hlam]
                  · linarith only [h10, h91, hlam]
                · linarith only [h90, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h0, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                rcases p77_3 (m.d 0 2) (by simp) with h97 | h97
                · rcases p77_3 (m.d 1 2) (by simp) with h98 | h98
                  · rcases p77_3 (m.d 2 3) (by simp) with h99 | h99
                    · linarith only [h99, hlam, p77_0]
                    · rcases p77_3 (m.d 2 4) (by simp) with h101 | h101
                      · linarith only [h101, h9, hlam]
                      · linarith only [h101, h14, hlam]
                  · linarith only [h98, hlam, p77_0]
                · linarith only [h3, h97, hlam]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h0, h75, hc01, hc45, hlam, hphi, ht0b, ht5b, p77_1]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                rcases p77_3 (m.d 0 2) (by simp) with h107 | h107
                · rcases p77_3 (m.d 1 2) (by simp) with h108 | h108
                  · rcases p77_3 (m.d 2 3) (by simp) with h109 | h109
                    · linarith only [h109, h8, hlam]
                    · rcases p77_3 (m.d 2 4) (by simp) with h111 | h111
                      · linarith only [h111, h9, hlam]
                      · linarith only [h111, h75, hlam]
                  · linarith only [h108, hlam, p77_0]
                · linarith only [h107, h5, hlam]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h3, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h8, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h14, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h73, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h4, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h9, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p77_1]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h1, h11, h14, hc01, hc25, hlam, hphi, ht0b, ht5b, p77_1]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h5, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h10, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p77_1]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h75, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [hlam, p77_0]
            · linarith only [h0, h11, h13, h14, h76, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h132 | h132
            · linarith only [h0, h11, h132, h75, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h11, h13, h132, h14, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
      · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
        · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
          · linarith only [h0, h13, h137, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h139 | h139
            · linarith only [h13, h135, h139, h9, hlam]
            · rcases h2bigk with h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h0, h135, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p141_1]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                rcases p141_3 (m.d 0 2) (by simp) with h144 | h144
                · rcases p141_3 (m.d 1 2) (by simp) with h145 | h145
                  · linarith only [h0, h145, hlam]
                  · linarith only [h145, h8, hlam]
                · linarith only [h144, hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                rcases p141_3 (m.d 0 2) (by simp) with h149 | h149
                · rcases p141_3 (m.d 1 2) (by simp) with h150 | h150
                  · linarith only [h0, h150, hlam]
                  · linarith only [h150, h9, hlam]
                · linarith only [h149, hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                rcases p141_3 (m.d 0 2) (by simp) with h154 | h154
                · rcases p141_3 (m.d 1 2) (by simp) with h155 | h155
                  · linarith only [h0, h155, hlam]
                  · linarith only [h10, h155, hlam]
                · linarith only [h154, hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h0, hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h0, h136, h139, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p141_1]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                rcases p141_3 (m.d 0 2) (by simp) with h162 | h162
                · rcases p141_3 (m.d 1 2) (by simp) with h163 | h163
                  · rcases p141_3 (m.d 2 3) (by simp) with h164 | h164
                    · linarith only [h164, h8, hlam]
                    · linarith only [h135, h164, hlam]
                  · linarith only [h163, hlam, p141_0]
                · linarith only [h162, h4, hlam]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                rcases p141_3 (m.d 0 2) (by simp) with h169 | h169
                · rcases p141_3 (m.d 1 2) (by simp) with h170 | h170
                  · rcases p141_3 (m.d 2 3) (by simp) with h171 | h171
                    · linarith only [h171, h8, hlam]
                    · linarith only [h136, h171, hlam]
                  · linarith only [h170, hlam, p141_0]
                · linarith only [h169, h5, hlam]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h3, hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h8, hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h0, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p141_1]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h0, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p141_1]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h4, hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h9, hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h135, hlam, p141_1]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h137, hlam, p141_1]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h5, hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h10, hlam, p141_0]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h136, hlam, p141_1]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [h0, h10, h135, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p141_1]
              · have p141_0 := h141c.1
                have p141_1 := h141c.2.1
                have p141_2 := h141c.2.2.1
                have p141_3 := h141c.2.2.2
                linarith only [hlam, p141_0]
        · linarith only [h0, h12, h135, h136, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
        · linarith only [h0, h11, h135, h192, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h194 | h194
          · linarith only [h11, h13, h135, h194, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h196 | h196
            · linarith only [h11, h13, h196, hlam]
            · rcases h2bigk with h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [hlam, p198_0]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h0, h11, h135, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p198_1]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h11, h13, h135, h3, h6, h7, hlam, p198_2]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                rcases p198_3 (m.d 0 2) (by simp) with h202 | h202
                · rcases p198_3 (m.d 1 2) (by simp) with h203 | h203
                  · linarith only [h0, h203, hlam]
                  · linarith only [h203, h9, hlam]
                · linarith only [h202, hlam, p198_0]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                rcases p198_3 (m.d 0 2) (by simp) with h207 | h207
                · rcases p198_3 (m.d 1 2) (by simp) with h208 | h208
                  · linarith only [h0, h208, hlam]
                  · linarith only [h10, h208, hlam]
                · linarith only [h207, hlam, p198_0]
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
                rcases p198_3 (m.d 0 2) (by simp) with h214 | h214
                · rcases p198_3 (m.d 1 2) (by simp) with h215 | h215
                  · rcases p198_3 (m.d 2 3) (by simp) with h216 | h216
                    · linarith only [h216, hlam, p198_0]
                    · rcases p198_3 (m.d 2 4) (by simp) with h218 | h218
                      · linarith only [h218, h9, hlam]
                      · linarith only [h135, h218, hlam]
                  · linarith only [h215, hlam, p198_0]
                · linarith only [h214, h3, hlam]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                rcases p198_3 (m.d 0 2) (by simp) with h223 | h223
                · rcases p198_3 (m.d 1 2) (by simp) with h224 | h224
                  · rcases p198_3 (m.d 2 3) (by simp) with h225 | h225
                    · linarith only [h225, h8, hlam]
                    · rcases p198_3 (m.d 2 4) (by simp) with h227 | h227
                      · linarith only [h227, hlam, p198_0]
                      · rcases p198_3 (m.d 2 5) (by simp) with h229 | h229
                        · linarith only [h10, h229, hlam]
                        · linarith only [h194, h229, hlam]
                  · linarith only [h224, hlam, p198_0]
                · linarith only [h223, h4, hlam]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                rcases p198_3 (m.d 0 2) (by simp) with h234 | h234
                · rcases p198_3 (m.d 1 2) (by simp) with h235 | h235
                  · rcases p198_3 (m.d 2 3) (by simp) with h236 | h236
                    · linarith only [h236, h8, hlam]
                    · rcases p198_3 (m.d 2 4) (by simp) with h238 | h238
                      · linarith only [h238, h9, hlam]
                      · rcases p198_3 (m.d 2 5) (by simp) with h240 | h240
                        · linarith only [h240, hlam, p198_0]
                        · rcases h4bigk with h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [hlam, p242_0]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            rcases p242_3 (m.d 0 4) (by simp) with h244 | h244
                            · rcases p242_3 (m.d 1 4) (by simp) with h245 | h245
                              · linarith only [h2, h245, hlam]
                              · rcases p242_3 (m.d 2 4) (by simp) with h247 | h247
                                · linarith only [h247, h4, hlam]
                                · rcases p242_3 (m.d 3 4) (by simp) with h249 | h249
                                  · linarith only [h249, h6, hlam]
                                  · rcases p242_3 (m.d 4 5) (by simp) with h251 | h251
                                    · linarith only [h251, h7, hlam]
                                    · linarith only [h13, h251, hlam]
                            · linarith only [h2, h244, hlam]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            rcases p242_3 (m.d 0 4) (by simp) with h255 | h255
                            · rcases p242_3 (m.d 1 4) (by simp) with h256 | h256
                              · linarith only [h2, h256, hlam]
                              · linarith only [h256, h9, hlam]
                            · linarith only [h255, h4, hlam]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            rcases p242_3 (m.d 0 4) (by simp) with h260 | h260
                            · rcases p242_3 (m.d 1 4) (by simp) with h261 | h261
                              · linarith only [h2, h261, hlam]
                              · linarith only [h11, h261, hlam]
                            · linarith only [h260, h6, hlam]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h0, h11, h13, h135, h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p242_1]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h2, hlam, p242_1]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [hlam, p242_0]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h13, hc24, hc45, hlam, hphi, p242_1]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h13, h135, h3, h6, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p242_1]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h13, hlam, p242_0]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h4, hlam, p242_1]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h9, hlam, p242_1]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [hlam, p242_0]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h135, hlam, p242_1]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h194, hlam, p242_0]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h6, hlam, p242_1]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h11, hlam, p242_0]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h0, h12, h196, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p242_1]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [hlam, p242_0]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h196, hlam, p242_0]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h7, hlam, p242_0]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h0, h11, h135, h3, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p242_1]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            rcases p242_3 (m.d 0 4) (by simp) with h283 | h283
                            · rcases p242_3 (m.d 1 4) (by simp) with h284 | h284
                              · linarith only [h13, h284, hlam]
                              · linarith only [h284, h9, hlam]
                            · linarith only [h283, h4, hlam]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [h0, h135, h3, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p242_1]
                          · have p242_0 := h242c.1
                            have p242_1 := h242c.2.1
                            have p242_2 := h242c.2.2.1
                            have p242_3 := h242c.2.2.2
                            linarith only [hlam, p242_0]
                  · linarith only [h235, hlam, p198_0]
                · linarith only [h234, h5, hlam]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h3, hlam, p198_0]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h8, hlam, p198_0]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [hlam, p198_0]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h135, hlam, p198_0]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h192, hlam, p198_0]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h4, hlam, p198_0]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h9, hlam, p198_0]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p198_1]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [hlam, p198_0]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h194, hlam, p198_1]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h5, hlam, p198_0]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h10, hlam, p198_0]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p198_1]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p198_1]
              · have p198_0 := h198c.1
                have p198_1 := h198c.2.1
                have p198_2 := h198c.2.2.1
                have p198_3 := h198c.2.2.2
                linarith only [hlam, p198_0]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h307 | h307
    · linarith only [h11, h12, h307, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h309 | h309
      · rcases m.htr 2 3 5 (by decide) (by decide) with h310 | h310
        · linarith only [h0, h12, h310, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h312 | h312
          · linarith only [h11, h12, h307, h312, h9, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h314 | h314
            · linarith only [h0, h3, h307, h309, h314, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h2bigk with h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h0, h309, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p316_1]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                rcases p316_3 (m.d 0 2) (by simp) with h319 | h319
                · rcases p316_3 (m.d 1 2) (by simp) with h320 | h320
                  · linarith only [h0, h320, hlam]
                  · linarith only [h320, h8, hlam]
                · linarith only [h319, hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                rcases p316_3 (m.d 0 2) (by simp) with h324 | h324
                · rcases p316_3 (m.d 1 2) (by simp) with h325 | h325
                  · linarith only [h0, h325, hlam]
                  · linarith only [h325, h9, hlam]
                · linarith only [h324, hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                rcases p316_3 (m.d 0 2) (by simp) with h329 | h329
                · rcases p316_3 (m.d 1 2) (by simp) with h330 | h330
                  · linarith only [h0, h330, hlam]
                  · linarith only [h10, h330, hlam]
                · linarith only [h329, hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h0, hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h0, h309, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p316_1]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                rcases p316_3 (m.d 0 2) (by simp) with h337 | h337
                · rcases p316_3 (m.d 1 2) (by simp) with h338 | h338
                  · rcases p316_3 (m.d 2 3) (by simp) with h339 | h339
                    · linarith only [h339, h8, hlam]
                    · linarith only [h309, h339, hlam]
                  · linarith only [h338, hlam, p316_0]
                · linarith only [h337, h4, hlam]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h0, h309, h310, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p316_1]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h3, hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h8, hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h0, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p316_1]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h310, hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h4, hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h9, hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h309, hlam, p316_1]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h312, hlam, p316_1]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h5, hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h10, hlam, p316_0]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p316_1]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [h0, h10, h309, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p316_1]
              · have p316_0 := h316c.1
                have p316_1 := h316c.2.1
                have p316_2 := h316c.2.2.1
                have p316_3 := h316c.2.2.2
                linarith only [hlam, p316_0]
      · linarith only [h11, h12, h309, hc23, hc35, hlam, hphi]

end R2N4
