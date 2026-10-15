import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
  · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
    · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
      · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
        · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
          · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
            · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
              · linarith only [h0, h10, h17, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h0, h10, h14, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
              · linarith only [h0, h16, h20, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                · linarith only [h0, h11, h22, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                  · linarith only [h0, h10, h13, h16, h22, h24, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h10, h13, h15, h16, h24, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
            · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
              · linarith only [h0, h10, h28, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h1, h14, h27, h28, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
              · linarith only [h0, h27, h31, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                · linarith only [h13, h15, h27, h33, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h13, h15, h35, hlam]
                  · rcases h0bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h15, h4, h7, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h13, h15, h27, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h13, h15, h27, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h13, h15, h27, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h13, h15, h27, h7, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, h13, h15, h27, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, h13, h15, h27, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h1, hlam, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h4, hlam, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h13, h15, h27, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, h13, h15, h27, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h2, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h5, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h7, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, h13, h15, h27, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h3, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h6, hlam, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h8, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h9, hlam, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h63 | h63
          · linarith only [h0, h13, h14, h4, h63, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
            · rcases m.htr 2 3 5 (by decide) (by decide) with h66 | h66
              · linarith only [h0, h10, h66, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                · linarith only [h0, h11, h63, h68, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h70 | h70
                  · linarith only [h0, h13, h14, h4, h63, h70, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [hlam, p72_0]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h14, h4, h7, h70, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h10, h14, h7, h70, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h10, h14, h70, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h13, h14, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p72_1]
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
                      linarith only [h13, h14, h7, h70, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h0, h13, h14, h70, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h0, h13, h14, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h1, hlam, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h4, hlam, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [hlam, p72_0]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h13, h14, h70, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h0, h13, h14, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h2, hlam, p72_0]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h5, hlam, p72_0]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h7, hlam, p72_0]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [hlam, p72_0]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h13, h14, h8, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h3, hlam, p72_0]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h6, hlam, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h8, hlam, p72_0]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [h9, hlam, p72_1]
                    · have p72_0 := h72c.1
                      have p72_1 := h72c.2.1
                      have p72_2 := h72c.2.2.1
                      have p72_3 := h72c.2.2.2
                      linarith only [hlam, p72_0]
            · linarith only [h13, h14, h65, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
        · linarith only [h0, h13, h4, h7, h99, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
          · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
            · linarith only [h0, h10, h102, h13, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h104 | h104
              · linarith only [h10, h104, h99, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                · linarith only [h0, h106, h11, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h108 | h108
                  · rcases h0bigk with h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [hlam, p109_0]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h101, h106, h13, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p109_1]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h101, h106, h13, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p109_1]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h101, h106, h13, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p109_1]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      rcases p109_3 (m.d 0 1) (by simp) with h114 | h114
                      · rcases p109_3 (m.d 0 2) (by simp) with h115 | h115
                        · linarith only [h0, h115, hlam]
                        · linarith only [h115, h6, hlam]
                      · linarith only [h114, h3, hlam]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h0, hlam, p109_0]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [hlam, p109_0]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h101, h102, h106, h13, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p109_1]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h0, h101, h102, h106, h13, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p109_1]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      rcases p109_3 (m.d 0 1) (by simp) with h123 | h123
                      · rcases p109_3 (m.d 0 2) (by simp) with h124 | h124
                        · rcases p109_3 (m.d 0 3) (by simp) with h125 | h125
                          · linarith only [h125, h4, hlam]
                          · linarith only [h125, h8, hlam]
                        · linarith only [h124, h6, hlam]
                      · linarith only [h123, h3, hlam]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h1, hlam, p109_1]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h4, hlam, p109_1]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [hlam, p109_0]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h101, h102, h106, h13, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p109_1]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      rcases p109_3 (m.d 0 1) (by simp) with h134 | h134
                      · rcases p109_3 (m.d 0 2) (by simp) with h135 | h135
                        · rcases p109_3 (m.d 0 3) (by simp) with h136 | h136
                          · rcases p109_3 (m.d 0 4) (by simp) with h137 | h137
                            · linarith only [h137, h7, hlam]
                            · linarith only [h137, h9, hlam]
                          · linarith only [h136, h8, hlam]
                        · linarith only [h135, h6, hlam]
                      · linarith only [h134, h3, hlam]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h2, hlam, p109_0]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h5, hlam, p109_0]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h7, hlam, p109_0]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [hlam, p109_0]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      rcases p109_3 (m.d 0 1) (by simp) with h147 | h147
                      · rcases p109_3 (m.d 0 2) (by simp) with h148 | h148
                        · rcases p109_3 (m.d 0 3) (by simp) with h149 | h149
                          · rcases p109_3 (m.d 0 4) (by simp) with h150 | h150
                            · rcases p109_3 (m.d 0 5) (by simp) with h151 | h151
                              · linarith only [h151, h9, hlam]
                              · rcases h2bigk with h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h0, h101, h102, h106, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h101, h102, h106, h5, h8, h99, hlam, p109_1, p153_2]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h101, h106, h5, h8, h99, hlam, p109_1, p153_2]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  rcases p153_3 (m.d 0 2) (by simp) with h158 | h158
                                  · rcases p153_3 (m.d 1 2) (by simp) with h159 | h159
                                    · linarith only [h0, h159, hlam]
                                    · linarith only [h12, h159, hlam]
                                  · linarith only [h158, hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h0, hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  rcases p153_3 (m.d 0 2) (by simp) with h165 | h165
                                  · rcases p153_3 (m.d 1 2) (by simp) with h166 | h166
                                    · rcases p153_3 (m.d 2 3) (by simp) with h167 | h167
                                      · linarith only [h167, hlam, p153_0]
                                      · rcases p153_3 (m.d 2 4) (by simp) with h169 | h169
                                        · linarith only [h11, h169, hlam]
                                        · linarith only [h102, h169, hlam]
                                    · linarith only [h166, hlam, p153_0]
                                  · linarith only [h165, h4, hlam]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  rcases p153_3 (m.d 0 2) (by simp) with h174 | h174
                                  · rcases p153_3 (m.d 1 2) (by simp) with h175 | h175
                                    · rcases p153_3 (m.d 2 3) (by simp) with h176 | h176
                                      · linarith only [h10, h176, hlam]
                                      · rcases p153_3 (m.d 2 4) (by simp) with h178 | h178
                                        · linarith only [h178, hlam, p153_0]
                                        · rcases p153_3 (m.d 2 5) (by simp) with h180 | h180
                                          · linarith only [h12, h180, hlam]
                                          · linarith only [h106, h180, hlam]
                                    · linarith only [h175, hlam, p153_0]
                                  · linarith only [h174, h5, hlam]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p153_1, u5ehi2]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h4, hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h10, hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h102, hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h104, hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h5, hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h11, hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h101, h106, h4, h7, h8, h99, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p109_1, p153_1]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h106, hlam, p153_1]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h6, hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h12, hlam, p153_0]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h0, h4, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p109_1, p153_1]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [h0, h101, h106, h4, h7, h8, h99, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p109_1, p153_1]
                                · have p153_0 := h153c.1
                                  have p153_1 := h153c.2.1
                                  have p153_2 := h153c.2.2.1
                                  have p153_3 := h153c.2.2.2
                                  linarith only [hlam, p153_0]
                            · linarith only [h150, h9, hlam]
                          · linarith only [h149, h8, hlam]
                        · linarith only [h148, h6, hlam]
                      · linarith only [h147, h3, hlam]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h3, hlam, p109_0]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h6, hlam, p109_1]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h8, hlam, p109_0]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [h9, hlam, p109_1]
                    · have p109_0 := h109c.1
                      have p109_1 := h109c.2.1
                      have p109_2 := h109c.2.2.1
                      have p109_3 := h109c.2.2.2
                      linarith only [hlam, p109_0]
                  · linarith only [h101, h108, h13, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h211 | h211
            · linarith only [h10, h13, h211, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h213 | h213
              · linarith only [h0, h10, h13, h213, h4, h7, h99, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h215 | h215
                · linarith only [h0, h101, h11, h13, h215, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h217 | h217
                  · rcases h0bigk with h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [hlam, p218_0]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h6, hc01, hlam, hphi, ht0b, ht5b, p218_1, u5ehi2]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h10, h101, h13, h217, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p218_1]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h10, h101, h13, h217, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p218_1]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      rcases p218_3 (m.d 0 1) (by simp) with h223 | h223
                      · rcases p218_3 (m.d 0 2) (by simp) with h224 | h224
                        · linarith only [h0, h224, hlam]
                        · linarith only [h224, h6, hlam]
                      · linarith only [h223, h3, hlam]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h0, hlam, p218_0]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [hlam, p218_0]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h10, h101, h13, h217, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p218_1]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h0, h10, h101, h13, h217, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p218_1]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      rcases p218_3 (m.d 0 1) (by simp) with h232 | h232
                      · rcases p218_3 (m.d 0 2) (by simp) with h233 | h233
                        · rcases p218_3 (m.d 0 3) (by simp) with h234 | h234
                          · linarith only [h234, h4, hlam]
                          · linarith only [h234, h8, hlam]
                        · linarith only [h233, h6, hlam]
                      · linarith only [h232, h3, hlam]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h1, hlam, p218_1]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h4, hlam, p218_1]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [hlam, p218_0]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h10, h101, h13, h217, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p218_1]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      rcases p218_3 (m.d 0 1) (by simp) with h243 | h243
                      · rcases p218_3 (m.d 0 2) (by simp) with h244 | h244
                        · rcases p218_3 (m.d 0 3) (by simp) with h245 | h245
                          · rcases p218_3 (m.d 0 4) (by simp) with h246 | h246
                            · linarith only [h246, h7, hlam]
                            · linarith only [h246, h9, hlam]
                          · linarith only [h245, h8, hlam]
                        · linarith only [h244, h6, hlam]
                      · linarith only [h243, h3, hlam]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h2, hlam, p218_0]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h5, hlam, p218_0]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h7, hlam, p218_0]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [hlam, p218_0]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      rcases p218_3 (m.d 0 1) (by simp) with h256 | h256
                      · rcases p218_3 (m.d 0 2) (by simp) with h257 | h257
                        · rcases p218_3 (m.d 0 3) (by simp) with h258 | h258
                          · rcases p218_3 (m.d 0 4) (by simp) with h259 | h259
                            · rcases p218_3 (m.d 0 5) (by simp) with h260 | h260
                              · linarith only [h260, h9, hlam]
                              · rcases h2bigk with h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht5b, p262_1, u5ehi2]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h10, h101, h13, h217, h5, h8, hlam, p218_1, p262_2]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h101, h11, h217, h5, h8, hlam, p218_1, p262_2]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  rcases p262_3 (m.d 0 2) (by simp) with h267 | h267
                                  · rcases p262_3 (m.d 1 2) (by simp) with h268 | h268
                                    · linarith only [h0, h268, hlam]
                                    · linarith only [h12, h268, hlam]
                                  · linarith only [h267, hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h0, hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  rcases p262_3 (m.d 0 2) (by simp) with h274 | h274
                                  · rcases p262_3 (m.d 1 2) (by simp) with h275 | h275
                                    · rcases p262_3 (m.d 2 3) (by simp) with h276 | h276
                                      · linarith only [h276, hlam, p262_0]
                                      · rcases p262_3 (m.d 2 4) (by simp) with h278 | h278
                                        · linarith only [h11, h278, hlam]
                                        · linarith only [h211, h278, hlam]
                                    · linarith only [h275, hlam, p262_0]
                                  · linarith only [h274, h4, hlam]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  rcases p262_3 (m.d 0 2) (by simp) with h283 | h283
                                  · rcases p262_3 (m.d 1 2) (by simp) with h284 | h284
                                    · rcases p262_3 (m.d 2 3) (by simp) with h285 | h285
                                      · linarith only [h10, h285, hlam]
                                      · rcases p262_3 (m.d 2 4) (by simp) with h287 | h287
                                        · linarith only [h287, hlam, p262_0]
                                        · rcases p262_3 (m.d 2 5) (by simp) with h289 | h289
                                          · linarith only [h12, h289, hlam]
                                          · linarith only [h215, h289, hlam]
                                    · linarith only [h284, hlam, p262_0]
                                  · linarith only [h283, h5, hlam]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p262_1, u5ehi2]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h4, hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h10, hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h211, hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h213, hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h5, hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h11, hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h101, h11, h217, h4, h7, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p218_1, p262_1]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h215, hlam, p262_1]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h6, hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h12, hlam, p262_0]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h0, h12, h3, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p218_1, p262_1]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [h0, h101, h12, h217, h4, h7, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p218_1, p262_1]
                                · have p262_0 := h262c.1
                                  have p262_1 := h262c.2.1
                                  have p262_2 := h262c.2.2.1
                                  have p262_3 := h262c.2.2.2
                                  linarith only [hlam, p262_0]
                            · linarith only [h259, h9, hlam]
                          · linarith only [h258, h8, hlam]
                        · linarith only [h257, h6, hlam]
                      · linarith only [h256, h3, hlam]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h3, hlam, p218_0]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h6, hlam, p218_1]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h8, hlam, p218_0]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [h9, hlam, p218_1]
                    · have p218_0 := h218c.1
                      have p218_1 := h218c.2.1
                      have p218_2 := h218c.2.2.1
                      have p218_3 := h218c.2.2.2
                      linarith only [hlam, p218_0]
                  · rcases h0bigk with h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [hlam, p319_0]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h6, hc01, hlam, hphi, ht0b, ht5b, p319_1, u5ehi2]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h10, h13, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h10, h13, h217, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h10, h13, h217, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h0, hlam, p319_0]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [hlam, p319_0]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h8, hc02, hlam, hphi, ht0b, ht5b, p319_1, u5ehi3]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h0, h10, h13, h217, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h0, h10, h13, h217, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h1, hlam, p319_1]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h4, hlam, p319_1]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [hlam, p319_0]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h10, h13, h217, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h0, h10, h13, h217, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h2, hlam, p319_0]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h5, hlam, p319_0]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h7, hlam, p319_0]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [hlam, p319_0]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h10, h13, h217, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h3, hlam, p319_0]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h6, hlam, p319_1]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h8, hlam, p319_0]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [h9, hlam, p319_1]
                    · have p319_0 := h319c.1
                      have p319_1 := h319c.2.1
                      have p319_2 := h319c.2.2.1
                      have p319_3 := h319c.2.2.2
                      linarith only [hlam, p319_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
      · rcases m.htr 1 3 5 (by decide) (by decide) with h346 | h346
        · linarith only [h0, h10, h12, h346, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h348 | h348
          · linarith only [h0, h10, h12, h345, h348, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h350 | h350
            · linarith only [h0, h10, h12, h350, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h12, h345, h350, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h353 | h353
        · linarith only [h0, h11, h12, h345, h353, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h355 | h355
          · linarith only [h0, h11, h12, h355, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
            · linarith only [h0, h10, h12, h345, h357, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h359 | h359
              · linarith only [h0, h10, h12, h353, h359, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h361 | h361
                · linarith only [h0, h11, h361, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h363 | h363
                  · linarith only [h0, h11, h12, h361, h363, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [hlam, p365_0]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h363, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h363, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h363, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h11, h12, h357, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h0, hlam, p365_0]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [hlam, p365_0]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h363, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h0, h363, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h0, h11, h12, h357, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h1, hlam, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h4, hlam, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [hlam, p365_0]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h363, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h0, h11, h12, h357, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h2, hlam, p365_0]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h5, hlam, p365_0]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h7, hlam, p365_0]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [hlam, p365_0]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h11, h12, h357, h6, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h3, hlam, p365_0]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h6, hlam, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h8, hlam, p365_0]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h9, hlam, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [hlam, p365_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h391 | h391
    · linarith only [h0, h11, h391, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h393 | h393
      · linarith only [h10, h11, h393, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h395 | h395
        · linarith only [h0, h10, h11, h395, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h397 | h397
          · rcases m.htr 2 3 4 (by decide) (by decide) with h398 | h398
            · linarith only [h0, h10, h11, h393, h398, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h400 | h400
              · linarith only [h10, h391, h395, h400, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h402 | h402
                · rcases m.htr 3 4 5 (by decide) (by decide) with h403 | h403
                  · rcases h0bigk with h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c | h404c
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [hlam, p404_0]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h391, h398, h4, h402, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h10, h391, h398, h402, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h2, h397, hc01, hlam, hphi, ht0b, ht5b, p404_1, u5ehi4]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h10, h391, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h0, hlam, p404_0]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [hlam, p404_0]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h10, h391, h398, h402, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h0, h10, h391, h402, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h0, h10, h391, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h1, hlam, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h4, hlam, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [hlam, p404_0]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h10, h391, h402, h5, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h0, h10, h391, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h2, hlam, p404_0]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h5, hlam, p404_0]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h7, hlam, p404_0]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [hlam, p404_0]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h10, h391, h400, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h3, hlam, p404_0]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h6, hlam, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h8, hlam, p404_0]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [h9, hlam, p404_1]
                    · have p404_0 := h404c.1
                      have p404_1 := h404c.2.1
                      have p404_2 := h404c.2.2.1
                      have p404_3 := h404c.2.2.2
                      linarith only [hlam, p404_0]
                  · linarith only [h10, h391, h397, h398, h402, h403, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h10, h11, h4, h402, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h432 | h432
            · linarith only [h0, h10, h11, h432, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h434 | h434
              · linarith only [h0, h10, h11, h397, h4, h434, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h436 | h436
                · linarith only [h0, h10, h11, h397, h4, h432, h436, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h10, h11, h436, hc23, hc45, hlam, hphi, ht34]

end R2N4
