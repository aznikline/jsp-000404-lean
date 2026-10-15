import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
  · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
    · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
      · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
        · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
            · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
              · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                · linarith only [h0, h13, h16, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h13, h15, h16, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                · linarith only [h0, h10, h15, h19, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h3bigk with h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h0, h10, h12, h13, h15, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    rcases p21_3 (m.d 0 3) (by simp) with h24 | h24
                    · rcases p21_3 (m.d 1 3) (by simp) with h25 | h25
                      · linarith only [h1, h25, hlam]
                      · linarith only [h25, h8, hlam]
                    · linarith only [h24, h3, hlam]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    rcases p21_3 (m.d 0 3) (by simp) with h29 | h29
                    · rcases p21_3 (m.d 1 3) (by simp) with h30 | h30
                      · linarith only [h1, h30, hlam]
                      · linarith only [h10, h30, hlam]
                    · linarith only [h29, hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    rcases p21_3 (m.d 0 3) (by simp) with h34 | h34
                    · rcases p21_3 (m.d 1 3) (by simp) with h35 | h35
                      · linarith only [h1, h35, hlam]
                      · linarith only [h11, h35, hlam]
                    · linarith only [h34, hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h1, hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h1, h14, h19, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    rcases p21_3 (m.d 0 3) (by simp) with h42 | h42
                    · rcases p21_3 (m.d 1 3) (by simp) with h43 | h43
                      · rcases p21_3 (m.d 2 3) (by simp) with h44 | h44
                        · linarith only [h44, h8, hlam]
                        · linarith only [h13, h44, hlam]
                      · linarith only [h43, hlam, p21_0]
                    · linarith only [h42, h5, hlam]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    rcases p21_3 (m.d 0 3) (by simp) with h49 | h49
                    · rcases p21_3 (m.d 1 3) (by simp) with h50 | h50
                      · rcases p21_3 (m.d 2 3) (by simp) with h51 | h51
                        · linarith only [h51, h8, hlam]
                        · linarith only [h14, h51, hlam]
                      · linarith only [h50, hlam, p21_0]
                    · linarith only [h49, h6, hlam]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h3, hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h8, hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h0, h19, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h5, hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h10, hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h13, hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h19, hlam, p21_1]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h6, hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h11, hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h14, hlam, p21_0]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [h0, h11, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                  · have p21_0 := h21c.1
                    have p21_1 := h21c.2.1
                    have p21_2 := h21c.2.2.1
                    have p21_3 := h21c.2.2.2
                    linarith only [hlam, p21_0]
            · linarith only [h0, h11, h13, h14, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h72 | h72
            · linarith only [h0, h10, h13, h72, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h74 | h74
              · rcases m.htr 3 4 5 (by decide) (by decide) with h75 | h75
                · rcases h3bigk with h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h10, h13, h74, hc03, hc45, hlam, hphi, ht0b, ht5b, p76_1]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    rcases p76_3 (m.d 0 3) (by simp) with h79 | h79
                    · rcases p76_3 (m.d 1 3) (by simp) with h80 | h80
                      · linarith only [h1, h80, hlam]
                      · linarith only [h8, h80, hlam]
                    · linarith only [h3, h79, hlam]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    rcases p76_3 (m.d 0 3) (by simp) with h84 | h84
                    · rcases p76_3 (m.d 1 3) (by simp) with h85 | h85
                      · linarith only [h1, h85, hlam]
                      · linarith only [h10, h85, hlam]
                    · linarith only [h84, hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    rcases p76_3 (m.d 0 3) (by simp) with h89 | h89
                    · rcases p76_3 (m.d 1 3) (by simp) with h90 | h90
                      · linarith only [h1, h90, hlam]
                      · linarith only [h11, h90, hlam]
                    · linarith only [h89, hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h1, hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    rcases p76_3 (m.d 0 3) (by simp) with h96 | h96
                    · rcases p76_3 (m.d 1 3) (by simp) with h97 | h97
                      · rcases p76_3 (m.d 2 3) (by simp) with h98 | h98
                        · linarith only [h8, h98, hlam]
                        · rcases p76_3 (m.d 3 4) (by simp) with h100 | h100
                          · linarith only [h10, h100, hlam]
                          · linarith only [h100, h13, hlam]
                      · linarith only [h8, h97, hlam]
                    · linarith only [h3, h96, hlam]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h0, h72, h75, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h0, h72, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h3, hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h8, hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h13, hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h72, hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h5, hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h10, hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h0, h10, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h0, h10, h72, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h6, hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h11, hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h0, h11, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [h75, hlam, p76_0]
                  · have p76_0 := h76c.1
                    have p76_1 := h76c.2.1
                    have p76_2 := h76c.2.2.1
                    have p76_3 := h76c.2.2.2
                    linarith only [hlam, p76_0]
                · linarith only [h13, h74, h75, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
                · linarith only [h0, h10, h123, h74, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h10, h12, h123, h13, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
          · rcases m.htr 2 3 5 (by decide) (by decide) with h127 | h127
            · rcases m.htr 2 4 5 (by decide) (by decide) with h128 | h128
              · linarith only [h12, h128, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
                · linarith only [h0, h12, h126, h130, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                · rcases h3bigk with h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    rcases p132_3 (m.d 0 3) (by simp) with h134 | h134
                    · rcases p132_3 (m.d 1 3) (by simp) with h135 | h135
                      · linarith only [h1, h135, hlam]
                      · rcases p132_3 (m.d 2 3) (by simp) with h137 | h137
                        · linarith only [h137, h3, hlam]
                        · rcases p132_3 (m.d 3 4) (by simp) with h139 | h139
                          · linarith only [h139, h5, hlam]
                          · rcases p132_3 (m.d 3 5) (by simp) with h141 | h141
                            · linarith only [h141, h6, hlam]
                            · rcases h4bigk with h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                rcases p143_3 (m.d 0 4) (by simp) with h145 | h145
                                · rcases p143_3 (m.d 1 4) (by simp) with h146 | h146
                                  · linarith only [h146, h2, hlam]
                                  · rcases p143_3 (m.d 2 4) (by simp) with h148 | h148
                                    · linarith only [h148, h4, hlam]
                                    · rcases p143_3 (m.d 3 4) (by simp) with h150 | h150
                                      · linarith only [h150, h5, hlam]
                                      · rcases p143_3 (m.d 4 5) (by simp) with h152 | h152
                                        · linarith only [h152, h7, hlam]
                                        · linarith only [h12, h152, hlam]
                                · linarith only [h145, h2, hlam]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                rcases p143_3 (m.d 0 4) (by simp) with h156 | h156
                                · rcases p143_3 (m.d 1 4) (by simp) with h157 | h157
                                  · linarith only [h157, h2, hlam]
                                  · linarith only [h157, h9, hlam]
                                · linarith only [h156, h4, hlam]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                rcases p143_3 (m.d 0 4) (by simp) with h161 | h161
                                · rcases p143_3 (m.d 1 4) (by simp) with h162 | h162
                                  · linarith only [h162, h2, hlam]
                                  · linarith only [h10, h162, hlam]
                                · linarith only [h161, h5, hlam]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h12, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi3]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h2, hlam, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h12, hc24, hc45, hlam, hphi, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h0, h12, h3, h5, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h12, hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h4, hlam, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h9, hlam, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h0, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h128, hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h5, hlam, p143_1]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h10, hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h126, hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h130, hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h7, hlam, p143_0]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi3]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                rcases p143_3 (m.d 0 4) (by simp) with h184 | h184
                                · rcases p143_3 (m.d 1 4) (by simp) with h185 | h185
                                  · linarith only [h12, h185, hlam]
                                  · linarith only [h185, h9, hlam]
                                · linarith only [h184, h4, hlam]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                rcases p143_3 (m.d 0 4) (by simp) with h189 | h189
                                · rcases p143_3 (m.d 1 4) (by simp) with h190 | h190
                                  · linarith only [h12, h190, hlam]
                                  · linarith only [h10, h190, hlam]
                                · linarith only [h189, h5, hlam]
                              · have p143_0 := h143c.1
                                have p143_1 := h143c.2.1
                                have p143_2 := h143c.2.2.1
                                have p143_3 := h143c.2.2.2
                                linarith only [hlam, p143_0]
                    · linarith only [h1, h134, hlam]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    rcases p132_3 (m.d 0 3) (by simp) with h196 | h196
                    · rcases p132_3 (m.d 1 3) (by simp) with h197 | h197
                      · linarith only [h1, h197, hlam]
                      · linarith only [h197, h8, hlam]
                    · linarith only [h196, h3, hlam]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    rcases p132_3 (m.d 0 3) (by simp) with h201 | h201
                    · rcases p132_3 (m.d 1 3) (by simp) with h202 | h202
                      · linarith only [h1, h202, hlam]
                      · linarith only [h10, h202, hlam]
                    · linarith only [h201, hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    rcases p132_3 (m.d 0 3) (by simp) with h206 | h206
                    · rcases p132_3 (m.d 1 3) (by simp) with h207 | h207
                      · linarith only [h1, h207, hlam]
                      · linarith only [h11, h207, hlam]
                    · linarith only [h206, hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h1, hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h1, h127, h130, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    rcases p132_3 (m.d 0 3) (by simp) with h214 | h214
                    · rcases p132_3 (m.d 1 3) (by simp) with h215 | h215
                      · rcases p132_3 (m.d 2 3) (by simp) with h216 | h216
                        · linarith only [h216, h8, hlam]
                        · linarith only [h126, h216, hlam]
                      · linarith only [h215, hlam, p132_0]
                    · linarith only [h214, h5, hlam]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    rcases p132_3 (m.d 0 3) (by simp) with h221 | h221
                    · rcases p132_3 (m.d 1 3) (by simp) with h222 | h222
                      · rcases p132_3 (m.d 2 3) (by simp) with h223 | h223
                        · linarith only [h223, h8, hlam]
                        · linarith only [h127, h223, hlam]
                      · linarith only [h222, hlam, p132_0]
                    · linarith only [h221, h6, hlam]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h3, hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h8, hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h0, h130, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h5, hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h10, hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h126, hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h130, hlam, p132_1]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h6, hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h11, hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h127, hlam, p132_0]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [h0, h11, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                  · have p132_0 := h132c.1
                    have p132_1 := h132c.2.1
                    have p132_2 := h132c.2.2.1
                    have p132_3 := h132c.2.2.2
                    linarith only [hlam, p132_0]
            · linarith only [h0, h11, h126, h127, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h244 | h244
            · linarith only [h10, h12, h126, h244, h3, h5, h7, hc02, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
              · linarith only [h12, h246, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h248 | h248
                · linarith only [h10, h12, h248, hlam]
                · rcases h3bigk with h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h0, h10, h126, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p250_1]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h10, h12, h126, h5, h7, hlam, p250_2]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    rcases p250_3 (m.d 0 3) (by simp) with h254 | h254
                    · rcases p250_3 (m.d 1 3) (by simp) with h255 | h255
                      · linarith only [h1, h255, hlam]
                      · linarith only [h10, h255, hlam]
                    · linarith only [h254, hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    rcases p250_3 (m.d 0 3) (by simp) with h259 | h259
                    · rcases p250_3 (m.d 1 3) (by simp) with h260 | h260
                      · linarith only [h1, h260, hlam]
                      · linarith only [h11, h260, hlam]
                    · linarith only [h259, hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h1, hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    rcases p250_3 (m.d 0 3) (by simp) with h266 | h266
                    · rcases p250_3 (m.d 1 3) (by simp) with h267 | h267
                      · rcases p250_3 (m.d 2 3) (by simp) with h268 | h268
                        · linarith only [h268, h8, hlam]
                        · rcases p250_3 (m.d 3 4) (by simp) with h270 | h270
                          · linarith only [h10, h270, hlam]
                          · linarith only [h126, h270, hlam]
                      · linarith only [h267, h8, hlam]
                    · linarith only [h266, h3, hlam]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h1, h126, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p250_1]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h0, h126, h248, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p250_1]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h3, hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h8, hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h126, hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h244, hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h5, hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h10, hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h0, h10, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p250_1]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h248, hlam, p250_1]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h6, hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h11, hlam, p250_0]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h0, h11, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p250_1]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [h0, h11, h126, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p250_1]
                  · have p250_0 := h250c.1
                    have p250_1 := h250c.2.1
                    have p250_2 := h250c.2.2.1
                    have p250_3 := h250c.2.2.2
                    linarith only [hlam, p250_0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h292 | h292
        · linarith only [h10, h11, h292, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
          · rcases m.htr 2 3 5 (by decide) (by decide) with h295 | h295
            · linarith only [h10, h11, h295, hc23, hlam, hphi, ht12, u1ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h297 | h297
              · linarith only [h292, h297, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h299 | h299
                · linarith only [h292, h299, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · rcases h3bigk with h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    rcases p301_3 (m.d 0 3) (by simp) with h303 | h303
                    · rcases p301_3 (m.d 1 3) (by simp) with h304 | h304
                      · linarith only [h1, h304, hlam]
                      · rcases p301_3 (m.d 2 3) (by simp) with h306 | h306
                        · linarith only [h3, h306, hlam]
                        · rcases p301_3 (m.d 3 4) (by simp) with h308 | h308
                          · linarith only [h308, h5, hlam]
                          · rcases p301_3 (m.d 3 5) (by simp) with h310 | h310
                            · linarith only [h310, h6, hlam]
                            · linarith only [h11, h310, hlam]
                    · linarith only [h1, h303, hlam]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    rcases p301_3 (m.d 0 3) (by simp) with h314 | h314
                    · rcases p301_3 (m.d 1 3) (by simp) with h315 | h315
                      · linarith only [h1, h315, hlam]
                      · linarith only [h315, h8, hlam]
                    · linarith only [h3, h314, hlam]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h11, h294, h6, h8, hlam, p301_2]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h10, h11, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p301_1, u1ehi3]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h1, hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h11, h294, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p301_1]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h0, h11, h3, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p301_1]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h11, hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h3, hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h8, hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p301_1]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h295, hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h5, hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h10, hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h294, hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h299, hlam, p301_1]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h6, hlam, p301_0]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p301_1, u1ehi2]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [h0, h294, h3, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p301_1]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    rcases p301_3 (m.d 0 3) (by simp) with h339 | h339
                    · rcases p301_3 (m.d 1 3) (by simp) with h340 | h340
                      · linarith only [h11, h340, hlam]
                      · linarith only [h10, h340, hlam]
                    · linarith only [h339, h5, hlam]
                  · have p301_0 := h301c.1
                    have p301_1 := h301c.2.1
                    have p301_2 := h301c.2.2.1
                    have p301_3 := h301c.2.2.2
                    linarith only [hlam, p301_0]
          · linarith only [h10, h11, h294, hc23, hc35, hlam, hphi]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h346 | h346
      · rcases m.htr 1 4 5 (by decide) (by decide) with h347 | h347
        · rcases m.htr 2 3 4 (by decide) (by decide) with h348 | h348
          · linarith only [h10, h348, h8, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h350 | h350
            · rcases m.htr 2 4 5 (by decide) (by decide) with h351 | h351
              · rcases m.htr 3 4 5 (by decide) (by decide) with h352 | h352
                · rcases h3bigk with h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    rcases p353_3 (m.d 0 3) (by simp) with h355 | h355
                    · rcases p353_3 (m.d 1 3) (by simp) with h356 | h356
                      · linarith only [h1, h356, hlam]
                      · rcases p353_3 (m.d 2 3) (by simp) with h358 | h358
                        · linarith only [h3, h358, hlam]
                        · rcases p353_3 (m.d 3 4) (by simp) with h360 | h360
                          · linarith only [h360, h5, hlam]
                          · linarith only [h10, h360, hlam]
                    · linarith only [h1, h355, hlam]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    rcases p353_3 (m.d 0 3) (by simp) with h364 | h364
                    · rcases p353_3 (m.d 1 3) (by simp) with h365 | h365
                      · linarith only [h1, h365, hlam]
                      · linarith only [h365, h8, hlam]
                    · linarith only [h3, h364, hlam]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h0, h10, h3, h346, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p353_1, u1ehi4]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h10, h350, h5, h8, hlam, p353_2]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h1, hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h10, hc23, hc34, hlam, hphi, p353_1]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h10, hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h0, h10, h3, h352, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p353_1]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h3, hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h8, hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h348, hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h0, h352, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p353_1]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h5, hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h0, h3, h346, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p353_1, u1ehi4]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h0, h3, h350, h352, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p353_1]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    rcases p353_3 (m.d 0 3) (by simp) with h385 | h385
                    · rcases p353_3 (m.d 1 3) (by simp) with h386 | h386
                      · linarith only [h10, h386, hlam]
                      · linarith only [h346, h386, hlam]
                    · linarith only [h385, h6, hlam]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h6, hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h346, hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h350, hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [h352, hlam, p353_0]
                  · have p353_0 := h353c.1
                    have p353_1 := h353c.2.1
                    have p353_2 := h353c.2.2.1
                    have p353_3 := h353c.2.2.2
                    linarith only [hlam, p353_0]
                · linarith only [h0, h10, h3, h346, h352, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
              · linarith only [h2, h347, h348, h350, h351, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h3, h346, h350, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h10, h346, h347, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h399 | h399
        · rcases m.htr 2 3 4 (by decide) (by decide) with h400 | h400
          · linarith only [h10, h400, h8, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h402 | h402
            · linarith only [h346, h402, h8, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h404 | h404
              · rcases m.htr 3 4 5 (by decide) (by decide) with h405 | h405
                · rcases h3bigk with h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    rcases p406_3 (m.d 0 3) (by simp) with h408 | h408
                    · rcases p406_3 (m.d 1 3) (by simp) with h409 | h409
                      · linarith only [h1, h409, hlam]
                      · rcases p406_3 (m.d 2 3) (by simp) with h411 | h411
                        · linarith only [h3, h411, hlam]
                        · rcases p406_3 (m.d 3 4) (by simp) with h413 | h413
                          · linarith only [h413, h5, hlam]
                          · linarith only [h10, h413, hlam]
                    · linarith only [h1, h408, hlam]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    rcases p406_3 (m.d 0 3) (by simp) with h417 | h417
                    · rcases p406_3 (m.d 1 3) (by simp) with h418 | h418
                      · linarith only [h1, h418, hlam]
                      · linarith only [h418, h8, hlam]
                    · linarith only [h3, h417, hlam]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h0, h3, h346, h405, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p406_1, u1ehi2]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h0, h3, h346, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p406_1, u1ehi2]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h1, hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h346, h405, hc23, hc34, hlam, hphi, p406_1]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h10, hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h346, hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h3, hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h8, hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h400, hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h402, hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h5, hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p406_1, u1ehi2]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    rcases p406_3 (m.d 0 3) (by simp) with h436 | h436
                    · rcases p406_3 (m.d 1 3) (by simp) with h437 | h437
                      · linarith only [h10, h437, hlam]
                      · linarith only [h437, h8, hlam]
                    · linarith only [h3, h436, hlam]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h0, h3, h346, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p406_1, u1ehi2]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h6, hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [hc35, hlam, hphi, ht12, ht23, p406_1, u1ehi2]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    rcases p406_3 (m.d 0 3) (by simp) with h445 | h445
                    · rcases p406_3 (m.d 1 3) (by simp) with h446 | h446
                      · linarith only [h346, h446, hlam]
                      · linarith only [h446, h8, hlam]
                    · linarith only [h3, h445, hlam]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [h405, hlam, p406_0]
                  · have p406_0 := h406c.1
                    have p406_1 := h406c.2.1
                    have p406_2 := h406c.2.2.1
                    have p406_3 := h406c.2.2.2
                    linarith only [hlam, p406_0]
                · linarith only [h0, h404, h405, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h453 | h453
                · rcases h3bigk with h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    rcases p454_3 (m.d 0 3) (by simp) with h456 | h456
                    · rcases p454_3 (m.d 1 3) (by simp) with h457 | h457
                      · linarith only [h1, h457, hlam]
                      · rcases p454_3 (m.d 2 3) (by simp) with h459 | h459
                        · linarith only [h3, h459, hlam]
                        · rcases p454_3 (m.d 3 4) (by simp) with h461 | h461
                          · linarith only [h461, h5, hlam]
                          · linarith only [h10, h461, hlam]
                    · linarith only [h1, h456, hlam]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h10, h399, h400, h404, h5, hlam, p454_2]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h10, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p454_1, u1ehi2]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h0, h3, h346, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p454_1, u1ehi2]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h1, hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h0, h10, h3, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p454_1]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h10, hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h346, hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h3, hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h8, hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h400, hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h402, hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h5, hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p454_1, u1ehi2]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    rcases p454_3 (m.d 0 3) (by simp) with h480 | h480
                    · rcases p454_3 (m.d 1 3) (by simp) with h481 | h481
                      · linarith only [h10, h481, hlam]
                      · linarith only [h481, h8, hlam]
                    · linarith only [h3, h480, hlam]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h0, h3, h346, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p454_1, u1ehi2]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h6, hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [hc35, hlam, hphi, ht12, ht23, p454_1, u1ehi2]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    rcases p454_3 (m.d 0 3) (by simp) with h489 | h489
                    · rcases p454_3 (m.d 1 3) (by simp) with h490 | h490
                      · linarith only [h346, h490, hlam]
                      · linarith only [h490, h8, hlam]
                    · linarith only [h3, h489, hlam]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [h453, hlam, p454_0]
                  · have p454_0 := h454c.1
                    have p454_1 := h454c.2.1
                    have p454_2 := h454c.2.2.1
                    have p454_3 := h454c.2.2.2
                    linarith only [hlam, p454_0]
                · linarith only [h10, h399, h453, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h497 | h497
          · linarith only [h10, h497, h8, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h499 | h499
            · linarith only [h346, h499, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h501 | h501
              · linarith only [h399, h501, h9, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h503 | h503
                · linarith only [h399, h503, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · linarith only [h0, h10, h3, h5, h503, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h506 | h506
    · linarith only [h506, h8, h9, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h508 | h508
      · rcases m.htr 1 4 5 (by decide) (by decide) with h509 | h509
        · rcases m.htr 2 3 4 (by decide) (by decide) with h510 | h510
          · linarith only [h0, h4, h506, h510, h8, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h512 | h512
            · linarith only [h0, h3, h5, h510, h512, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h3, h5, h508, h510, h512, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h508, h509, h8, h9, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h516 | h516
        · rcases m.htr 2 3 4 (by decide) (by decide) with h517 | h517
          · linarith only [h0, h4, h517, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h519 | h519
            · linarith only [h0, h3, h5, h508, h517, h519, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h521 | h521
              · rcases m.htr 3 4 5 (by decide) (by decide) with h522 | h522
                · rcases h3bigk with h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    rcases p523_3 (m.d 0 3) (by simp) with h525 | h525
                    · rcases p523_3 (m.d 1 3) (by simp) with h526 | h526
                      · linarith only [h1, h526, hlam]
                      · rcases p523_3 (m.d 2 3) (by simp) with h528 | h528
                        · linarith only [h3, h528, hlam]
                        · rcases p523_3 (m.d 3 4) (by simp) with h530 | h530
                          · linarith only [h5, h530, hlam]
                          · linarith only [h506, h530, hlam]
                    · linarith only [h1, h525, hlam]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h5, h517, h8, h9, hlam, p523_2]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h0, h3, h517, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p523_1]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h0, h3, h508, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p523_1, u1ehi2]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h1, hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h517, h8, h9, hc23, hc34, hlam, hphi, p523_1]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h506, hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h508, hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h3, hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h8, hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h517, hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h519, hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h5, hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p523_1, u1ehi2]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    rcases p523_3 (m.d 0 3) (by simp) with h549 | h549
                    · rcases p523_3 (m.d 1 3) (by simp) with h550 | h550
                      · linarith only [h506, h550, hlam]
                      · linarith only [h550, h8, hlam]
                    · linarith only [h3, h549, hlam]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h0, h3, h5, h508, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p523_1, u1ehi2]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h6, hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [hc35, hlam, hphi, ht12, ht23, p523_1, u1ehi2]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    rcases p523_3 (m.d 0 3) (by simp) with h558 | h558
                    · rcases p523_3 (m.d 1 3) (by simp) with h559 | h559
                      · linarith only [h508, h559, hlam]
                      · linarith only [h559, h8, hlam]
                    · linarith only [h3, h558, hlam]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [h522, hlam, p523_0]
                  · have p523_0 := h523c.1
                    have p523_1 := h523c.2.1
                    have p523_2 := h523c.2.2.1
                    have p523_3 := h523c.2.2.2
                    linarith only [hlam, p523_0]
                · linarith only [h516, h517, h522, h9, hc14, hlam, hphi, u1ehi1]
              · linarith only [h516, h521, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h567 | h567
          · linarith only [h0, h3, h5, h516, h567, h7, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h569 | h569
            · linarith only [h0, h3, h5, h516, h569, h7, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h571 | h571
              · linarith only [h516, h571, h8, h9, hc24, hlam, hphi, ht12, u1ehi2]
              · linarith only [h0, h3, h5, h571, h7, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]

end R2N4
