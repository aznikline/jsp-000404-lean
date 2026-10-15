import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5068000 in
theorem r1l7_13_24_L_I_H_I_s7_x0_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
  · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
    · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
      · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
        · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
          · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
            · linarith only [h0, h14, h17, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h14, h16, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
            · linarith only [h0, h11, h16, h20, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h3bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h0, h11, h13, h14, h16, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                rcases p22_3 (m.d 0 3) (by simp) with h25 | h25
                · rcases p22_3 (m.d 1 3) (by simp) with h26 | h26
                  · linarith only [h1, h26, hlam]
                  · linarith only [h26, h9, hlam]
                · linarith only [h25, h4, hlam]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                rcases p22_3 (m.d 0 3) (by simp) with h30 | h30
                · rcases p22_3 (m.d 1 3) (by simp) with h31 | h31
                  · linarith only [h1, h31, hlam]
                  · linarith only [h11, h31, hlam]
                · linarith only [h30, hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                rcases p22_3 (m.d 0 3) (by simp) with h35 | h35
                · rcases p22_3 (m.d 1 3) (by simp) with h36 | h36
                  · linarith only [h1, h36, hlam]
                  · linarith only [h12, h36, hlam]
                · linarith only [h35, hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h1, hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h1, h15, h20, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                rcases p22_3 (m.d 0 3) (by simp) with h43 | h43
                · rcases p22_3 (m.d 1 3) (by simp) with h44 | h44
                  · rcases p22_3 (m.d 2 3) (by simp) with h45 | h45
                    · linarith only [h45, h9, hlam]
                    · linarith only [h14, h45, hlam]
                  · linarith only [h44, hlam, p22_0]
                · linarith only [h43, h6, hlam]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                rcases p22_3 (m.d 0 3) (by simp) with h50 | h50
                · rcases p22_3 (m.d 1 3) (by simp) with h51 | h51
                  · rcases p22_3 (m.d 2 3) (by simp) with h52 | h52
                    · linarith only [h52, h9, hlam]
                    · linarith only [h15, h52, hlam]
                  · linarith only [h51, hlam, p22_0]
                · linarith only [h50, h7, hlam]
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
                linarith only [hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h0, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h0, h20, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h6, hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h11, hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h14, hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h20, hlam, p22_1]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h7, hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h12, hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h15, hlam, p22_0]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [h0, h12, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
              · have p22_0 := h22c.1
                have p22_1 := h22c.2.1
                have p22_2 := h22c.2.2.1
                have p22_3 := h22c.2.2.2
                linarith only [hlam, p22_0]
        · linarith only [h0, h12, h14, h15, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
        · linarith only [h0, h11, h14, h73, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
          · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
            · rcases h3bigk with h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h11, h73, h76, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p77_1]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                rcases p77_3 (m.d 0 3) (by simp) with h80 | h80
                · rcases p77_3 (m.d 1 3) (by simp) with h81 | h81
                  · linarith only [h1, h81, hlam]
                  · linarith only [h81, h9, hlam]
                · linarith only [h4, h80, hlam]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                rcases p77_3 (m.d 0 3) (by simp) with h85 | h85
                · rcases p77_3 (m.d 1 3) (by simp) with h86 | h86
                  · linarith only [h1, h86, hlam]
                  · linarith only [h11, h86, hlam]
                · linarith only [h85, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                rcases p77_3 (m.d 0 3) (by simp) with h90 | h90
                · rcases p77_3 (m.d 1 3) (by simp) with h91 | h91
                  · linarith only [h1, h91, hlam]
                  · linarith only [h12, h91, hlam]
                · linarith only [h90, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h1, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                rcases p77_3 (m.d 0 3) (by simp) with h97 | h97
                · rcases p77_3 (m.d 1 3) (by simp) with h98 | h98
                  · rcases p77_3 (m.d 2 3) (by simp) with h99 | h99
                    · linarith only [h9, h99, hlam]
                    · rcases p77_3 (m.d 3 4) (by simp) with h101 | h101
                      · linarith only [h101, h11, hlam]
                      · linarith only [h101, h14, hlam]
                  · linarith only [h9, h98, hlam]
                · linarith only [h4, h97, hlam]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h0, h73, h76, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p77_1]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h0, h73, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p77_1]
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
                linarith only [h6, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h11, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h0, h11, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p77_1]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h0, h11, h73, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p77_1]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h7, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h12, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h0, h12, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p77_1]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [h76, hlam, p77_0]
              · have p77_0 := h77c.1
                have p77_1 := h77c.2.1
                have p77_2 := h77c.2.2.1
                have p77_3 := h77c.2.2.2
                linarith only [hlam, p77_0]
            · linarith only [h14, h75, h76, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
            · linarith only [h0, h11, h124, h75, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h11, h124, h13, h14, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
      · rcases m.htr 2 3 5 (by decide) (by decide) with h128 | h128
        · rcases m.htr 2 4 5 (by decide) (by decide) with h129 | h129
          · linarith only [h0, h10, h129, h13, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
            · linarith only [h10, h127, h13, h131, hlam]
            · rcases h3bigk with h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                rcases p133_3 (m.d 0 3) (by simp) with h135 | h135
                · rcases p133_3 (m.d 1 3) (by simp) with h136 | h136
                  · linarith only [h1, h136, hlam]
                  · rcases p133_3 (m.d 2 3) (by simp) with h138 | h138
                    · linarith only [h138, h4, hlam]
                    · rcases p133_3 (m.d 3 4) (by simp) with h140 | h140
                      · linarith only [h140, h6, hlam]
                      · rcases p133_3 (m.d 3 5) (by simp) with h142 | h142
                        · linarith only [h142, h7, hlam]
                        · rcases h4bigk with h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            rcases p144_3 (m.d 0 4) (by simp) with h146 | h146
                            · rcases p144_3 (m.d 1 4) (by simp) with h147 | h147
                              · linarith only [h147, h2, hlam]
                              · rcases p144_3 (m.d 2 4) (by simp) with h149 | h149
                                · linarith only [h149, h5, hlam]
                                · rcases p144_3 (m.d 3 4) (by simp) with h151 | h151
                                  · linarith only [h151, h6, hlam]
                                  · rcases p144_3 (m.d 4 5) (by simp) with h153 | h153
                                    · linarith only [h153, h8, hlam]
                                    · linarith only [h13, h153, hlam]
                            · linarith only [h146, h2, hlam]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            rcases p144_3 (m.d 0 4) (by simp) with h157 | h157
                            · rcases p144_3 (m.d 1 4) (by simp) with h158 | h158
                              · linarith only [h158, h2, hlam]
                              · linarith only [h10, h158, hlam]
                            · linarith only [h157, h5, hlam]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            rcases p144_3 (m.d 0 4) (by simp) with h162 | h162
                            · rcases p144_3 (m.d 1 4) (by simp) with h163 | h163
                              · linarith only [h163, h2, hlam]
                              · linarith only [h11, h163, hlam]
                            · linarith only [h162, h6, hlam]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h0, h10, h127, h13, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h2, hlam, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h127, h13, hc34, hc45, hlam, hphi, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h0, h13, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h13, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h5, hlam, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h10, hlam, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h0, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h129, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h6, hlam, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h11, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h127, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h131, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h8, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h0, h4, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h0, h127, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h0, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hlam, p144_0]
                · linarith only [h1, h135, hlam]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                rcases p133_3 (m.d 0 3) (by simp) with h189 | h189
                · rcases p133_3 (m.d 1 3) (by simp) with h190 | h190
                  · linarith only [h1, h190, hlam]
                  · linarith only [h190, h9, hlam]
                · linarith only [h189, h4, hlam]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                rcases p133_3 (m.d 0 3) (by simp) with h194 | h194
                · rcases p133_3 (m.d 1 3) (by simp) with h195 | h195
                  · linarith only [h1, h195, hlam]
                  · linarith only [h11, h195, hlam]
                · linarith only [h194, hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                rcases p133_3 (m.d 0 3) (by simp) with h199 | h199
                · rcases p133_3 (m.d 1 3) (by simp) with h200 | h200
                  · linarith only [h1, h200, hlam]
                  · linarith only [h12, h200, hlam]
                · linarith only [h199, hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h1, hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h1, h128, h131, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p133_1]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                rcases p133_3 (m.d 0 3) (by simp) with h207 | h207
                · rcases p133_3 (m.d 1 3) (by simp) with h208 | h208
                  · rcases p133_3 (m.d 2 3) (by simp) with h209 | h209
                    · linarith only [h209, h9, hlam]
                    · linarith only [h127, h209, hlam]
                  · linarith only [h208, hlam, p133_0]
                · linarith only [h207, h6, hlam]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                rcases p133_3 (m.d 0 3) (by simp) with h214 | h214
                · rcases p133_3 (m.d 1 3) (by simp) with h215 | h215
                  · rcases p133_3 (m.d 2 3) (by simp) with h216 | h216
                    · linarith only [h216, h9, hlam]
                    · linarith only [h128, h216, hlam]
                  · linarith only [h215, hlam, p133_0]
                · linarith only [h214, h7, hlam]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h4, hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h9, hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h0, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p133_1]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h0, h131, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p133_1]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h6, hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h11, hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h127, hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h131, hlam, p133_1]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h7, hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h12, hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h128, hlam, p133_0]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [h0, h12, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p133_1]
              · have p133_0 := h133c.1
                have p133_1 := h133c.2.1
                have p133_2 := h133c.2.2.1
                have p133_3 := h133c.2.2.2
                linarith only [hlam, p133_0]
        · linarith only [h0, h12, h127, h128, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h237 | h237
        · linarith only [h11, h127, h13, h237, h4, h6, h8, hc02, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h239 | h239
          · linarith only [h0, h11, h127, h13, h239, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h241 | h241
            · linarith only [h11, h13, h241, hlam]
            · rcases h3bigk with h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h11, h127, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h11, h127, h13, h6, h8, hlam, p243_2]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                rcases p243_3 (m.d 0 3) (by simp) with h247 | h247
                · rcases p243_3 (m.d 1 3) (by simp) with h248 | h248
                  · linarith only [h1, h248, hlam]
                  · linarith only [h11, h248, hlam]
                · linarith only [h247, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                rcases p243_3 (m.d 0 3) (by simp) with h252 | h252
                · rcases p243_3 (m.d 1 3) (by simp) with h253 | h253
                  · linarith only [h1, h253, hlam]
                  · linarith only [h12, h253, hlam]
                · linarith only [h252, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h1, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                rcases p243_3 (m.d 0 3) (by simp) with h259 | h259
                · rcases p243_3 (m.d 1 3) (by simp) with h260 | h260
                  · rcases p243_3 (m.d 2 3) (by simp) with h261 | h261
                    · linarith only [h261, h9, hlam]
                    · rcases p243_3 (m.d 3 4) (by simp) with h263 | h263
                      · linarith only [h11, h263, hlam]
                      · linarith only [h127, h263, hlam]
                  · linarith only [h260, h9, hlam]
                · linarith only [h259, h4, hlam]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h1, h127, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h0, h127, h241, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h4, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h9, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h127, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h237, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h6, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h11, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h11, h13, h6, h8, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h241, hlam, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h7, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h12, hlam, p243_0]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h0, h12, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [h0, h12, h127, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p243_1]
              · have p243_0 := h243c.1
                have p243_1 := h243c.2.1
                have p243_2 := h243c.2.2.1
                have p243_3 := h243c.2.2.2
                linarith only [hlam, p243_0]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h285 | h285
    · linarith only [h11, h12, h285, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h287 | h287
      · rcases m.htr 2 3 5 (by decide) (by decide) with h288 | h288
        · linarith only [h0, h12, h288, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h290 | h290
          · linarith only [h10, h11, h12, h285, h290, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h292 | h292
            · linarith only [h0, h285, h287, h292, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h3bigk with h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                rcases p294_3 (m.d 0 3) (by simp) with h296 | h296
                · rcases p294_3 (m.d 1 3) (by simp) with h297 | h297
                  · linarith only [h1, h297, hlam]
                  · rcases p294_3 (m.d 2 3) (by simp) with h299 | h299
                    · linarith only [h299, h4, hlam]
                    · rcases p294_3 (m.d 3 4) (by simp) with h301 | h301
                      · linarith only [h301, h6, hlam]
                      · rcases p294_3 (m.d 3 5) (by simp) with h303 | h303
                        · linarith only [h303, h7, hlam]
                        · linarith only [h12, h303, hlam]
                · linarith only [h1, h296, hlam]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                rcases p294_3 (m.d 0 3) (by simp) with h307 | h307
                · rcases p294_3 (m.d 1 3) (by simp) with h308 | h308
                  · linarith only [h1, h308, hlam]
                  · linarith only [h308, h9, hlam]
                · linarith only [h307, h4, hlam]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h11, h12, h292, h6, h8, hlam, p294_2]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h0, h11, h12, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p294_1]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h1, hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h12, hc23, hc35, hlam, hphi, p294_1]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h0, h12, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p294_1]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h12, hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h4, hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h9, hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h0, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p294_1]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h288, hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h6, hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h11, hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h287, hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h292, hlam, p294_1]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h7, hlam, p294_0]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h0, h11, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p294_1]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [h0, h287, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p294_1]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                rcases p294_3 (m.d 0 3) (by simp) with h332 | h332
                · rcases p294_3 (m.d 1 3) (by simp) with h333 | h333
                  · linarith only [h12, h333, hlam]
                  · linarith only [h11, h333, hlam]
                · linarith only [h332, h6, hlam]
              · have p294_0 := h294c.1
                have p294_1 := h294c.2.1
                have p294_2 := h294c.2.2.1
                have p294_3 := h294c.2.2.2
                linarith only [hlam, p294_0]
      · linarith only [h11, h12, h287, hc23, hc35, hlam, hphi]

end R2N4
