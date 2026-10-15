import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
  · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
    · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
      · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
        · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
          · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
            · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
              · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h14, h17, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h14, h16, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                · linarith only [h0, h14, h16, h20, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
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
                    linarith only [h0, h11, h13, h16, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p22_1]
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
                    linarith only [h11, h14, h75, hc03, hc45, hlam, hphi, ht0b, ht5b, p77_1]
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
                · linarith only [h0, h11, h13, h14, h76, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
                · linarith only [h0, h11, h124, h14, h75, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h11, h124, h13, h14, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
          · rcases m.htr 2 3 5 (by decide) (by decide) with h128 | h128
            · rcases m.htr 2 4 5 (by decide) (by decide) with h129 | h129
              · linarith only [h129, h13, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
                · linarith only [h127, h13, h131, hc24, hlam, hphi, ht12, u1ehi3]
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
                            · rcases h5bigk with h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [hlam, p144_0]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h0, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p144_1, u1ehi4]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                rcases p144_3 (m.d 0 5) (by simp) with h147 | h147
                                · rcases p144_3 (m.d 1 5) (by simp) with h148 | h148
                                  · linarith only [h148, h3, hlam]
                                  · linarith only [h10, h148, hlam]
                                · linarith only [h147, h5, hlam]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                rcases p144_3 (m.d 0 5) (by simp) with h152 | h152
                                · rcases p144_3 (m.d 1 5) (by simp) with h153 | h153
                                  · linarith only [h153, h3, hlam]
                                  · linarith only [h12, h153, hlam]
                                · linarith only [h152, h7, hlam]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h0, h13, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p144_1, u1ehi3]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h3, hlam, p144_0]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [hlam, p144_0]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h129, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p144_1]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h12, h131, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p133_1, p144_1]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h13, hlam, p144_1]
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
                                linarith only [h0, h131, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p144_1]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h129, hlam, p144_1]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h7, hlam, p144_0]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h12, hlam, p144_0]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h128, hlam, p144_0]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [hlam, p144_0]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h131, hlam, p144_1]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h8, hlam, p144_0]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p144_1, u1ehi4]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h0, h128, h131, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p144_1]
                              · have p144_0 := h144c.1
                                have p144_1 := h144c.2.1
                                have p144_2 := h144c.2.2.1
                                have p144_3 := h144c.2.2.2
                                linarith only [h0, h131, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p144_1]
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
                    rcases p133_3 (m.d 0 3) (by simp) with h179 | h179
                    · rcases p133_3 (m.d 1 3) (by simp) with h180 | h180
                      · linarith only [h1, h180, hlam]
                      · linarith only [h180, h9, hlam]
                    · linarith only [h179, h4, hlam]
                  · have p133_0 := h133c.1
                    have p133_1 := h133c.2.1
                    have p133_2 := h133c.2.2.1
                    have p133_3 := h133c.2.2.2
                    rcases p133_3 (m.d 0 3) (by simp) with h184 | h184
                    · rcases p133_3 (m.d 1 3) (by simp) with h185 | h185
                      · linarith only [h1, h185, hlam]
                      · linarith only [h11, h185, hlam]
                    · linarith only [h184, hlam, p133_0]
                  · have p133_0 := h133c.1
                    have p133_1 := h133c.2.1
                    have p133_2 := h133c.2.2.1
                    have p133_3 := h133c.2.2.2
                    rcases p133_3 (m.d 0 3) (by simp) with h189 | h189
                    · rcases p133_3 (m.d 1 3) (by simp) with h190 | h190
                      · linarith only [h1, h190, hlam]
                      · linarith only [h12, h190, hlam]
                    · linarith only [h189, hlam, p133_0]
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
                    rcases p133_3 (m.d 0 3) (by simp) with h197 | h197
                    · rcases p133_3 (m.d 1 3) (by simp) with h198 | h198
                      · rcases p133_3 (m.d 2 3) (by simp) with h199 | h199
                        · linarith only [h199, h9, hlam]
                        · linarith only [h127, h199, hlam]
                      · linarith only [h198, hlam, p133_0]
                    · linarith only [h197, h6, hlam]
                  · have p133_0 := h133c.1
                    have p133_1 := h133c.2.1
                    have p133_2 := h133c.2.2.1
                    have p133_3 := h133c.2.2.2
                    rcases p133_3 (m.d 0 3) (by simp) with h204 | h204
                    · rcases p133_3 (m.d 1 3) (by simp) with h205 | h205
                      · rcases p133_3 (m.d 2 3) (by simp) with h206 | h206
                        · linarith only [h206, h9, hlam]
                        · linarith only [h128, h206, hlam]
                      · linarith only [h205, hlam, p133_0]
                    · linarith only [h204, h7, hlam]
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
                    linarith only [h0, h10, h128, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p133_1]
                  · have p133_0 := h133c.1
                    have p133_1 := h133c.2.1
                    have p133_2 := h133c.2.2.1
                    have p133_3 := h133c.2.2.2
                    linarith only [hlam, p133_0]
            · linarith only [h0, h12, h127, h128, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
            · linarith only [h0, h11, h127, h227, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h229 | h229
              · linarith only [h13, h229, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h231 | h231
                · linarith only [h11, h13, h231, hlam]
                · rcases h3bigk with h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h0, h11, h127, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p233_1]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h11, h127, h13, h6, h8, hlam, p233_2]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    rcases p233_3 (m.d 0 3) (by simp) with h237 | h237
                    · rcases p233_3 (m.d 1 3) (by simp) with h238 | h238
                      · linarith only [h1, h238, hlam]
                      · linarith only [h11, h238, hlam]
                    · linarith only [h237, hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    rcases p233_3 (m.d 0 3) (by simp) with h242 | h242
                    · rcases p233_3 (m.d 1 3) (by simp) with h243 | h243
                      · linarith only [h1, h243, hlam]
                      · linarith only [h12, h243, hlam]
                    · linarith only [h242, hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h1, hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    rcases p233_3 (m.d 0 3) (by simp) with h249 | h249
                    · rcases p233_3 (m.d 1 3) (by simp) with h250 | h250
                      · rcases p233_3 (m.d 2 3) (by simp) with h251 | h251
                        · linarith only [h251, h9, hlam]
                        · rcases p233_3 (m.d 3 4) (by simp) with h253 | h253
                          · linarith only [h11, h253, hlam]
                          · linarith only [h127, h253, hlam]
                      · linarith only [h250, h9, hlam]
                    · linarith only [h249, h4, hlam]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h1, h127, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p233_1]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h0, h127, h231, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p233_1]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h4, hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h9, hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h127, hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h227, hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h6, hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h11, hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h0, h11, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p233_1]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h231, hlam, p233_1]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h7, hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h12, hlam, p233_0]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h0, h12, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p233_1]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [h0, h12, h127, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p233_1]
                  · have p233_0 := h233c.1
                    have p233_1 := h233c.2.1
                    have p233_2 := h233c.2.2.1
                    have p233_3 := h233c.2.2.2
                    linarith only [hlam, p233_0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h275 | h275
        · linarith only [h11, h12, h275, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h277 | h277
          · rcases m.htr 2 3 5 (by decide) (by decide) with h278 | h278
            · linarith only [h12, h278, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h280 | h280
              · linarith only [h275, h280, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h282 | h282
                · linarith only [h275, h282, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · rcases h3bigk with h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    rcases p284_3 (m.d 0 3) (by simp) with h286 | h286
                    · rcases p284_3 (m.d 1 3) (by simp) with h287 | h287
                      · linarith only [h1, h287, hlam]
                      · rcases p284_3 (m.d 2 3) (by simp) with h289 | h289
                        · linarith only [h289, h4, hlam]
                        · rcases p284_3 (m.d 3 4) (by simp) with h291 | h291
                          · linarith only [h291, h6, hlam]
                          · rcases p284_3 (m.d 3 5) (by simp) with h293 | h293
                            · linarith only [h293, h7, hlam]
                            · linarith only [h12, h293, hlam]
                    · linarith only [h1, h286, hlam]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    rcases p284_3 (m.d 0 3) (by simp) with h297 | h297
                    · rcases p284_3 (m.d 1 3) (by simp) with h298 | h298
                      · linarith only [h1, h298, hlam]
                      · linarith only [h298, h9, hlam]
                    · linarith only [h297, h4, hlam]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h12, h277, h282, h6, h8, h9, hlam, p284_2]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h0, h11, h12, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi3]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h1, hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h12, h277, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p284_1]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h0, h12, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p284_1]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h12, hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h4, hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h9, hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h0, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p284_1]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h278, hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h6, hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h11, hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h277, hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h282, hlam, p284_1]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h7, hlam, p284_0]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi2]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [h0, h277, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p284_1]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    rcases p284_3 (m.d 0 3) (by simp) with h322 | h322
                    · rcases p284_3 (m.d 1 3) (by simp) with h323 | h323
                      · linarith only [h12, h323, hlam]
                      · linarith only [h11, h323, hlam]
                    · linarith only [h322, h6, hlam]
                  · have p284_0 := h284c.1
                    have p284_1 := h284c.2.1
                    have p284_2 := h284c.2.2.1
                    have p284_3 := h284c.2.2.2
                    linarith only [hlam, p284_0]
          · linarith only [h11, h12, h277, hc23, hc35, hlam, hphi]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h329 | h329
      · rcases m.htr 1 4 5 (by decide) (by decide) with h330 | h330
        · rcases m.htr 2 3 4 (by decide) (by decide) with h331 | h331
          · linarith only [h11, h329, h331, hc23, hlam, hphi, ht12, u1ehi4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h333 | h333
            · rcases m.htr 2 4 5 (by decide) (by decide) with h334 | h334
              · rcases m.htr 3 4 5 (by decide) (by decide) with h335 | h335
                · rcases h3bigk with h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    rcases p336_3 (m.d 0 3) (by simp) with h338 | h338
                    · rcases p336_3 (m.d 1 3) (by simp) with h339 | h339
                      · linarith only [h1, h339, hlam]
                      · rcases p336_3 (m.d 2 3) (by simp) with h341 | h341
                        · linarith only [h341, h4, hlam]
                        · rcases p336_3 (m.d 3 4) (by simp) with h343 | h343
                          · linarith only [h343, h6, hlam]
                          · linarith only [h11, h343, hlam]
                    · linarith only [h1, h338, hlam]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    rcases p336_3 (m.d 0 3) (by simp) with h347 | h347
                    · rcases p336_3 (m.d 1 3) (by simp) with h348 | h348
                      · linarith only [h1, h348, hlam]
                      · linarith only [h348, h9, hlam]
                    · linarith only [h347, h4, hlam]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h0, h11, h329, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p336_1, u1ehi4]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h11, h333, h6, h9, hlam, p336_2]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h1, hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h11, hc23, hc34, hlam, hphi, p336_1]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h11, hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h0, h11, h335, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p336_1]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h4, hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h9, hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h331, hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h0, h335, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p336_1]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h6, hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h0, h329, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p336_1, u1ehi4]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h0, h333, h335, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p336_1]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    rcases p336_3 (m.d 0 3) (by simp) with h368 | h368
                    · rcases p336_3 (m.d 1 3) (by simp) with h369 | h369
                      · linarith only [h11, h369, hlam]
                      · linarith only [h329, h369, hlam]
                    · linarith only [h368, h7, hlam]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h7, hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h329, hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h333, hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [h335, hlam, p336_0]
                  · have p336_0 := h336c.1
                    have p336_1 := h336c.2.1
                    have p336_2 := h336c.2.2.1
                    have p336_3 := h336c.2.2.2
                    linarith only [hlam, p336_0]
                · linarith only [h11, h335, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · linarith only [h0, h11, h329, h330, h331, h333, h334, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h11, h329, h333, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h11, h329, h330, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h382 | h382
        · rcases m.htr 2 3 4 (by decide) (by decide) with h383 | h383
          · linarith only [h0, h11, h383, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h385 | h385
            · linarith only [h329, h385, h9, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h387 | h387
              · rcases m.htr 3 4 5 (by decide) (by decide) with h388 | h388
                · rcases h3bigk with h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    rcases p389_3 (m.d 0 3) (by simp) with h391 | h391
                    · rcases p389_3 (m.d 1 3) (by simp) with h392 | h392
                      · linarith only [h1, h392, hlam]
                      · rcases p389_3 (m.d 2 3) (by simp) with h394 | h394
                        · linarith only [h394, h4, hlam]
                        · rcases p389_3 (m.d 3 4) (by simp) with h396 | h396
                          · linarith only [h396, h6, hlam]
                          · linarith only [h11, h396, hlam]
                    · linarith only [h1, h391, hlam]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    rcases p389_3 (m.d 0 3) (by simp) with h400 | h400
                    · rcases p389_3 (m.d 1 3) (by simp) with h401 | h401
                      · linarith only [h1, h401, hlam]
                      · linarith only [h401, h9, hlam]
                    · linarith only [h4, h400, hlam]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h0, h329, h388, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p389_1, u1ehi2]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h0, h329, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p389_1, u1ehi2]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h1, hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h329, h388, hc23, hc34, hlam, hphi, p389_1]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h11, hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h329, hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h4, hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h9, hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h383, hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h385, hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h6, hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p389_1, u1ehi2]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    rcases p389_3 (m.d 0 3) (by simp) with h419 | h419
                    · rcases p389_3 (m.d 1 3) (by simp) with h420 | h420
                      · linarith only [h11, h420, hlam]
                      · linarith only [h420, h9, hlam]
                    · linarith only [h4, h419, hlam]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h0, h329, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p389_1, u1ehi2]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h7, hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [hc35, hlam, hphi, ht12, ht23, p389_1, u1ehi2]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    rcases p389_3 (m.d 0 3) (by simp) with h428 | h428
                    · rcases p389_3 (m.d 1 3) (by simp) with h429 | h429
                      · linarith only [h329, h429, hlam]
                      · linarith only [h429, h9, hlam]
                    · linarith only [h4, h428, hlam]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [h388, hlam, p389_0]
                  · have p389_0 := h389c.1
                    have p389_1 := h389c.2.1
                    have p389_2 := h389c.2.2.1
                    have p389_3 := h389c.2.2.2
                    linarith only [hlam, p389_0]
                · linarith only [h11, h382, h388, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h436 | h436
                · rcases h3bigk with h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    rcases p437_3 (m.d 0 3) (by simp) with h439 | h439
                    · rcases p437_3 (m.d 1 3) (by simp) with h440 | h440
                      · linarith only [h1, h440, hlam]
                      · rcases p437_3 (m.d 2 3) (by simp) with h442 | h442
                        · linarith only [h4, h442, hlam]
                        · rcases p437_3 (m.d 3 4) (by simp) with h444 | h444
                          · linarith only [h444, h6, hlam]
                          · linarith only [h11, h444, hlam]
                    · linarith only [h1, h439, hlam]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h11, h382, h383, h387, h6, hlam, p437_2]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h0, h11, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi2]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h0, h329, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi2]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h1, hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h329, hc23, hc35, hlam, hphi, p437_1]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h11, hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h329, hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h4, hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h9, hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h383, hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h385, hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h6, hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [hc34, hlam, hphi, ht12, ht23, p437_1, u1ehi2]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    rcases p437_3 (m.d 0 3) (by simp) with h463 | h463
                    · rcases p437_3 (m.d 1 3) (by simp) with h464 | h464
                      · linarith only [h11, h464, hlam]
                      · linarith only [h464, h9, hlam]
                    · linarith only [h4, h463, hlam]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h0, h329, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi2]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h7, hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [hc35, hlam, hphi, ht12, ht23, p437_1, u1ehi2]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    rcases p437_3 (m.d 0 3) (by simp) with h472 | h472
                    · rcases p437_3 (m.d 1 3) (by simp) with h473 | h473
                      · linarith only [h329, h473, hlam]
                      · linarith only [h473, h9, hlam]
                    · linarith only [h4, h472, hlam]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [h436, hlam, p437_0]
                  · have p437_0 := h437c.1
                    have p437_1 := h437c.2.1
                    have p437_2 := h437c.2.2.1
                    have p437_3 := h437c.2.2.2
                    linarith only [hlam, p437_0]
                · linarith only [h11, h382, h436, hc14, hlam, hphi, u1ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h480 | h480
          · linarith only [h11, h480, hc23, hlam, hphi, ht12, u1ehi2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h482 | h482
            · linarith only [h329, h482, h9, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h484 | h484
              · linarith only [h11, h382, h484, hc24, hlam, hphi, ht12, u1ehi2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h486 | h486
                · linarith only [h11, h382, h486, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                · linarith only [h11, h486, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h489 | h489
    · rcases m.htr 1 3 5 (by decide) (by decide) with h490 | h490
      · linarith only [h10, h490, h9, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h492 | h492
        · linarith only [h10, h489, h492, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h494 | h494
          · linarith only [h0, h10, h494, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h489, h494, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h497 | h497
      · linarith only [h10, h497, h9, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h499 | h499
        · rcases m.htr 2 3 4 (by decide) (by decide) with h500 | h500
          · linarith only [h489, h500, hc23, hlam, hphi, ht12, u1ehi2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h502 | h502
            · linarith only [h0, h10, h497, h5, h502, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h504 | h504
              · rcases m.htr 3 4 5 (by decide) (by decide) with h505 | h505
                · rcases h3bigk with h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    rcases p506_3 (m.d 0 3) (by simp) with h508 | h508
                    · rcases p506_3 (m.d 1 3) (by simp) with h509 | h509
                      · linarith only [h1, h509, hlam]
                      · rcases p506_3 (m.d 2 3) (by simp) with h511 | h511
                        · linarith only [h4, h511, hlam]
                        · rcases p506_3 (m.d 3 4) (by simp) with h513 | h513
                          · linarith only [h513, h6, hlam]
                          · linarith only [h489, h513, hlam]
                    · linarith only [h1, h508, hlam]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h10, h500, h504, h6, h9, hlam, p506_2]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h0, h10, h4, h500, h504, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p506_1]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h0, h4, h497, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p506_1, u1ehi2]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h1, hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h10, h500, h504, h9, hc23, hc34, hlam, hphi, p506_1]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h489, hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h497, hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h4, hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h9, hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h500, hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h502, hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h6, hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p506_1, u1ehi2]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    rcases p506_3 (m.d 0 3) (by simp) with h532 | h532
                    · rcases p506_3 (m.d 1 3) (by simp) with h533 | h533
                      · linarith only [h489, h533, hlam]
                      · linarith only [h533, h9, hlam]
                    · linarith only [h4, h532, hlam]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h0, h4, h497, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p506_1, u1ehi2]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h7, hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [hc35, hlam, hphi, ht12, ht23, p506_1, u1ehi2]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    rcases p506_3 (m.d 0 3) (by simp) with h541 | h541
                    · rcases p506_3 (m.d 1 3) (by simp) with h542 | h542
                      · linarith only [h497, h542, hlam]
                      · linarith only [h542, h9, hlam]
                    · linarith only [h4, h541, hlam]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [h505, hlam, p506_0]
                  · have p506_0 := h506c.1
                    have p506_1 := h506c.2.1
                    have p506_2 := h506c.2.2.1
                    have p506_3 := h506c.2.2.2
                    linarith only [hlam, p506_0]
                · linarith only [h10, h499, h500, h504, h505, hc14, hlam, hphi, u1ehi1]
              · linarith only [h0, h10, h4, h489, h499, h504, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h550 | h550
          · linarith only [h0, h10, h5, h550, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h552 | h552
            · linarith only [h0, h10, h5, h552, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h554 | h554
              · linarith only [h499, h554, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h556 | h556
                · linarith only [h10, h554, h556, h9, hc23, hc34, hlam, hphi]
                · linarith only [h0, h4, h489, h556, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]

end R2N4
