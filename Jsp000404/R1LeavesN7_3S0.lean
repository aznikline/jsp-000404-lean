import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
  · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
    · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
      · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
        · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
          · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
            · linarith only [h0, h10, h16, h19, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h16, h18, h19, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
            · linarith only [h0, h10, h13, h18, h22, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h1bigk with h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h10, h17, hc01, hc35, hlam, hphi, ht0b, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h13, h15, h16, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h15, h16, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                rcases p24_3 (m.d 0 1) (by simp) with h29 | h29
                · rcases p24_3 (m.d 1 2) (by simp) with h30 | h30
                  · linarith only [h0, h30, hlam]
                  · linarith only [h12, h30, hlam]
                · linarith only [h29, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h0, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h13, h15, h16, h18, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h0, h15, h16, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h0, h15, h16, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h1, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h10, hlam, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h15, h16, h18, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h0, h10, h15, h16, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h2, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h11, hlam, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h13, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h0, h10, h13, h15, h16, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h3, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h12, hlam, p24_1]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h14, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h15, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [hlam, p24_0]
        · linarith only [h0, h10, h14, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
        · linarith only [h0, h10, h13, h16, h55, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
          · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
            · rcases h1bigk with h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h10, h13, h55, h58, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h13, h55, h58, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                rcases p59_3 (m.d 0 1) (by simp) with h63 | h63
                · rcases p59_3 (m.d 1 2) (by simp) with h64 | h64
                  · linarith only [h0, h64, hlam]
                  · linarith only [h11, h64, hlam]
                · linarith only [h63, hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                rcases p59_3 (m.d 0 1) (by simp) with h68 | h68
                · rcases p59_3 (m.d 1 2) (by simp) with h69 | h69
                  · linarith only [h0, h69, hlam]
                  · linarith only [h12, h69, hlam]
                · linarith only [h68, hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h0, hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h13, h55, h58, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p59_1]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h0, h11, h57, hc01, hc45, hlam, hphi, ht0b, ht5b, p59_1]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h0, h14, h55, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h1, hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h10, hlam, p59_1]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h1, h11, h57, hc01, hc45, hlam, hphi, ht0b, ht5b, p59_1]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h0, h10, h14, h55, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h2, hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h11, hlam, p59_1]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h13, hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h14, h2, h55, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h3, hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h12, hlam, p59_1]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h14, hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h15, hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [hlam, p59_0]
            · linarith only [h0, h11, h57, h58, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h94 | h94
            · linarith only [h0, h10, h13, h16, h57, h94, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h0, h10, h13, h15, h16, h94, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
      · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
        · rcases m.htr 2 4 5 (by decide) (by decide) with h99 | h99
          · linarith only [h0, h11, h15, h99, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h101 | h101
            · linarith only [h101, h11, h15, h97, hlam]
            · rcases h1bigk with h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h10, h101, h98, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p103_1]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                rcases p103_3 (m.d 0 1) (by simp) with h106 | h106
                · rcases p103_3 (m.d 1 2) (by simp) with h107 | h107
                  · linarith only [h0, h107, hlam]
                  · linarith only [h10, h107, hlam]
                · linarith only [h106, hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                rcases p103_3 (m.d 0 1) (by simp) with h111 | h111
                · rcases p103_3 (m.d 1 2) (by simp) with h112 | h112
                  · linarith only [h0, h112, hlam]
                  · linarith only [h11, h112, hlam]
                · linarith only [h111, hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                rcases p103_3 (m.d 0 1) (by simp) with h116 | h116
                · rcases p103_3 (m.d 1 2) (by simp) with h117 | h117
                  · linarith only [h0, h117, hlam]
                  · linarith only [h117, h12, hlam]
                · linarith only [h116, hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h0, hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h0, h10, h101, h98, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p103_1]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                rcases p103_3 (m.d 0 1) (by simp) with h124 | h124
                · rcases p103_3 (m.d 1 2) (by simp) with h125 | h125
                  · rcases p103_3 (m.d 1 3) (by simp) with h126 | h126
                    · linarith only [h10, h126, hlam]
                    · linarith only [h126, h13, hlam]
                  · linarith only [h11, h125, hlam]
                · linarith only [h124, h2, hlam]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                rcases p103_3 (m.d 0 1) (by simp) with h131 | h131
                · rcases p103_3 (m.d 1 2) (by simp) with h132 | h132
                  · rcases p103_3 (m.d 1 3) (by simp) with h133 | h133
                    · linarith only [h10, h133, hlam]
                    · linarith only [h133, h14, hlam]
                  · linarith only [h12, h132, hlam]
                · linarith only [h131, h3, hlam]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h1, hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h10, hlam, p103_1]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                rcases p103_3 (m.d 0 1) (by simp) with h141 | h141
                · rcases p103_3 (m.d 1 2) (by simp) with h142 | h142
                  · rcases p103_3 (m.d 1 3) (by simp) with h143 | h143
                    · rcases p103_3 (m.d 1 4) (by simp) with h144 | h144
                      · linarith only [h13, h144, hlam]
                      · rcases p103_3 (m.d 1 5) (by simp) with h146 | h146
                        · linarith only [h14, h146, hlam]
                        · linarith only [h146, h15, hlam]
                    · linarith only [h13, h143, hlam]
                  · linarith only [h11, h142, hlam]
                · linarith only [h141, h2, hlam]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                rcases p103_3 (m.d 0 1) (by simp) with h152 | h152
                · rcases p103_3 (m.d 1 2) (by simp) with h153 | h153
                  · rcases p103_3 (m.d 1 3) (by simp) with h154 | h154
                    · rcases p103_3 (m.d 1 4) (by simp) with h155 | h155
                      · linarith only [h13, h155, hlam]
                      · rcases p103_3 (m.d 1 5) (by simp) with h157 | h157
                        · linarith only [h14, h157, hlam]
                        · rcases h3bigk with h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, h15, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p103_1, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            rcases p159_3 (m.d 0 3) (by simp) with h162 | h162
                            · rcases p159_3 (m.d 1 3) (by simp) with h163 | h163
                              · linarith only [h1, h163, hlam]
                              · linarith only [h10, h163, hlam]
                            · linarith only [h162, h4, hlam]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            rcases p159_3 (m.d 0 3) (by simp) with h167 | h167
                            · rcases p159_3 (m.d 1 3) (by simp) with h168 | h168
                              · linarith only [h1, h168, hlam]
                              · linarith only [h13, h168, hlam]
                            · linarith only [h167, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            rcases p159_3 (m.d 0 3) (by simp) with h172 | h172
                            · rcases p159_3 (m.d 1 3) (by simp) with h173 | h173
                              · linarith only [h1, h173, hlam]
                              · linarith only [h14, h173, hlam]
                            · linarith only [h172, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h1, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h1, h101, h98, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            rcases p159_3 (m.d 0 3) (by simp) with h180 | h180
                            · rcases p159_3 (m.d 1 3) (by simp) with h181 | h181
                              · rcases p159_3 (m.d 2 3) (by simp) with h182 | h182
                                · linarith only [h10, h182, hlam]
                                · linarith only [h182, h97, hlam]
                              · linarith only [h181, hlam, p159_0]
                            · linarith only [h180, h7, hlam]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            rcases p159_3 (m.d 0 3) (by simp) with h187 | h187
                            · rcases p159_3 (m.d 1 3) (by simp) with h188 | h188
                              · rcases p159_3 (m.d 2 3) (by simp) with h189 | h189
                                · linarith only [h10, h189, hlam]
                                · linarith only [h189, h98, hlam]
                              · linarith only [h188, hlam, p159_0]
                            · linarith only [h187, h8, hlam]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h4, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h10, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, h10, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, h10, h101, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h7, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h13, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h97, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h101, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h8, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h14, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h98, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, h10, h14, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                    · linarith only [h14, h154, hlam]
                  · linarith only [h12, h153, hlam]
                · linarith only [h152, h3, hlam]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h2, hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h11, hlam, p103_1]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h13, hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h15, hlam, p103_1]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h3, hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h12, hlam, p103_1]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h14, hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                rcases p103_3 (m.d 0 1) (by simp) with h220 | h220
                · rcases p103_3 (m.d 1 2) (by simp) with h221 | h221
                  · rcases p103_3 (m.d 1 3) (by simp) with h222 | h222
                    · rcases p103_3 (m.d 1 4) (by simp) with h223 | h223
                      · linarith only [h15, h223, hlam]
                      · rcases p103_3 (m.d 1 5) (by simp) with h225 | h225
                        · rcases h3bigk with h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h11, h14, h97, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p103_1, p226_1]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            rcases p226_3 (m.d 0 3) (by simp) with h229 | h229
                            · rcases p226_3 (m.d 1 3) (by simp) with h230 | h230
                              · linarith only [h1, h230, hlam]
                              · linarith only [h10, h230, hlam]
                            · linarith only [h229, h4, hlam]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h11, h15, h7, h9, h97, hlam, p103_1, p226_2]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            rcases p226_3 (m.d 0 3) (by simp) with h235 | h235
                            · rcases p226_3 (m.d 1 3) (by simp) with h236 | h236
                              · linarith only [h1, h236, hlam]
                              · linarith only [h14, h236, hlam]
                            · linarith only [h235, hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h1, hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h1, h98, hc01, hc35, hlam, hphi, ht0b, ht5b, p226_1]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            rcases p226_3 (m.d 0 3) (by simp) with h243 | h243
                            · rcases p226_3 (m.d 1 3) (by simp) with h244 | h244
                              · rcases p226_3 (m.d 2 3) (by simp) with h245 | h245
                                · linarith only [h10, h245, hlam]
                                · linarith only [h245, h97, hlam]
                              · linarith only [h244, hlam, p226_0]
                            · linarith only [h243, h7, hlam]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            rcases p226_3 (m.d 0 3) (by simp) with h250 | h250
                            · rcases p226_3 (m.d 1 3) (by simp) with h251 | h251
                              · rcases p226_3 (m.d 2 3) (by simp) with h252 | h252
                                · linarith only [h10, h252, hlam]
                                · linarith only [h252, h98, hlam]
                              · linarith only [h251, hlam, p226_0]
                            · linarith only [h250, h8, hlam]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h4, hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h10, hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h0, h10, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p226_1]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h0, h10, h101, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p226_1]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h7, hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h13, hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h97, hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h101, hlam, p226_1]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h8, hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h14, hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h98, hlam, p226_0]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [h0, h10, h14, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p226_1]
                          · have p226_0 := h226c.1
                            have p226_1 := h226c.2.1
                            have p226_2 := h226c.2.2.1
                            have p226_3 := h226c.2.2.2
                            linarith only [hlam, p226_0]
                        · linarith only [h15, h225, hlam]
                    · linarith only [h13, h222, hlam]
                  · linarith only [h11, h221, hlam]
                · linarith only [h2, h220, hlam]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [hlam, p103_0]
        · linarith only [h0, h10, h14, h97, h98, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h278 | h278
        · linarith only [h0, h10, h13, h278, h97, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h280 | h280
          · linarith only [h0, h13, h15, h280, h5, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h282 | h282
            · linarith only [h13, h15, h282, hlam]
            · rcases h1bigk with h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h10, h13, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h13, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                rcases p284_3 (m.d 0 1) (by simp) with h288 | h288
                · rcases p284_3 (m.d 1 2) (by simp) with h289 | h289
                  · linarith only [h0, h289, hlam]
                  · linarith only [h11, h289, hlam]
                · linarith only [h288, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                rcases p284_3 (m.d 0 1) (by simp) with h293 | h293
                · rcases p284_3 (m.d 1 2) (by simp) with h294 | h294
                  · linarith only [h0, h294, hlam]
                  · linarith only [h12, h294, hlam]
                · linarith only [h293, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h0, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h14, h282, h97, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h0, h13, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h0, h14, h282, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h1, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h10, hlam, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h1, h13, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h0, h10, h14, h282, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h2, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h11, hlam, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h13, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h15, hlam, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h3, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h12, hlam, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h14, hlam, p284_0]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [h13, h3, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p284_1]
              · have p284_0 := h284c.1
                have p284_1 := h284c.2.1
                have p284_2 := h284c.2.2.1
                have p284_3 := h284c.2.2.2
                linarith only [hlam, p284_0]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h318 | h318
    · linarith only [h13, h14, h318, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
      · rcases m.htr 2 3 5 (by decide) (by decide) with h321 | h321
        · linarith only [h10, h14, h321, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h323 | h323
          · linarith only [h0, h11, h318, h323, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h325 | h325
            · linarith only [h10, h14, h318, h320, h325, hlam]
            · rcases h1bigk with h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h10, h320, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p327_1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                rcases p327_3 (m.d 0 1) (by simp) with h330 | h330
                · rcases p327_3 (m.d 1 2) (by simp) with h331 | h331
                  · linarith only [h0, h331, hlam]
                  · linarith only [h10, h331, hlam]
                · linarith only [h330, hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                rcases p327_3 (m.d 0 1) (by simp) with h335 | h335
                · rcases p327_3 (m.d 1 2) (by simp) with h336 | h336
                  · linarith only [h0, h336, hlam]
                  · linarith only [h11, h336, hlam]
                · linarith only [h335, hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                rcases p327_3 (m.d 0 1) (by simp) with h340 | h340
                · rcases p327_3 (m.d 1 2) (by simp) with h341 | h341
                  · linarith only [h0, h341, hlam]
                  · linarith only [h12, h341, hlam]
                · linarith only [h340, hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h0, hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h0, h10, h320, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p327_1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                rcases p327_3 (m.d 0 1) (by simp) with h348 | h348
                · rcases p327_3 (m.d 1 2) (by simp) with h349 | h349
                  · rcases p327_3 (m.d 1 3) (by simp) with h350 | h350
                    · linarith only [h10, h350, hlam]
                    · linarith only [h13, h350, hlam]
                  · linarith only [h11, h349, hlam]
                · linarith only [h2, h348, hlam]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h0, h10, h14, h320, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p327_1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h1, hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h10, hlam, p327_1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h14, h325, hc14, hc45, hlam, hphi, p327_1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h14, hlam, p327_1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h2, hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h11, hlam, p327_1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h13, hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h318, hlam, p327_1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h3, hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h12, hlam, p327_1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h10, h3, h320, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p327_1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                rcases p327_3 (m.d 0 1) (by simp) with h369 | h369
                · rcases p327_3 (m.d 1 2) (by simp) with h370 | h370
                  · rcases p327_3 (m.d 1 3) (by simp) with h371 | h371
                    · linarith only [h14, h371, hlam]
                    · linarith only [h13, h371, hlam]
                  · linarith only [h11, h370, hlam]
                · linarith only [h2, h369, hlam]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hlam, p327_0]
      · linarith only [h0, h13, h14, h320, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h378 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 4 5 (by decide) (by decide) with h379 | h379
  · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
    · linarith only [h0, h13, h378, h380, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h382 | h382
      · rcases m.htr 2 4 5 (by decide) (by decide) with h383 | h383
        · rcases m.htr 3 4 5 (by decide) (by decide) with h384 | h384
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
              linarith only [h10, h382, h384, hc01, hc45, hlam, hphi, ht0b, ht5b, p385_1]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              rcases p385_3 (m.d 0 1) (by simp) with h388 | h388
              · rcases p385_3 (m.d 1 2) (by simp) with h389 | h389
                · linarith only [h0, h389, hlam]
                · linarith only [h10, h389, hlam]
              · linarith only [h388, hlam, p385_0]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              rcases p385_3 (m.d 0 1) (by simp) with h393 | h393
              · rcases p385_3 (m.d 1 2) (by simp) with h394 | h394
                · linarith only [h0, h394, hlam]
                · linarith only [h11, h394, hlam]
              · linarith only [h393, hlam, p385_0]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              rcases p385_3 (m.d 0 1) (by simp) with h398 | h398
              · rcases p385_3 (m.d 1 2) (by simp) with h399 | h399
                · linarith only [h0, h399, hlam]
                · linarith only [h12, h399, hlam]
              · linarith only [h398, hlam, p385_0]
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
              linarith only [h0, h10, h382, h384, hc01, hc45, hlam, hphi, ht0b, ht5b, p385_1]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [h0, h10, h13, h382, h384, hc01, hc45, hlam, hphi, ht0b, ht5b, p385_1]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              rcases p385_3 (m.d 0 1) (by simp) with h407 | h407
              · rcases p385_3 (m.d 1 2) (by simp) with h408 | h408
                · rcases p385_3 (m.d 1 3) (by simp) with h409 | h409
                  · linarith only [h10, h409, hlam]
                  · linarith only [h378, h409, hlam]
                · linarith only [h12, h408, hlam]
              · linarith only [h3, h407, hlam]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [h1, hlam, p385_0]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [h10, hlam, p385_1]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [hlam, p385_0]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [h13, hlam, p385_1]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [h0, h12, h13, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p385_1]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [h2, hlam, p385_0]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [h11, hlam, p385_1]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [h10, h2, h382, h384, hc01, hc45, hlam, hphi, ht0b, ht5b, p385_1]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [hlam, p385_0]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              rcases p385_3 (m.d 0 1) (by simp) with h423 | h423
              · rcases p385_3 (m.d 1 2) (by simp) with h424 | h424
                · rcases p385_3 (m.d 1 3) (by simp) with h425 | h425
                  · linarith only [h13, h425, hlam]
                  · linarith only [h378, h425, hlam]
                · linarith only [h12, h424, hlam]
              · linarith only [h3, h423, hlam]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [h3, hlam, p385_0]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [h12, hlam, p385_1]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [h378, hlam, p385_0]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [h379, hlam, p385_0]
            · have p385_0 := h385c.1
              have p385_1 := h385c.2.1
              have p385_2 := h385c.2.2.1
              have p385_3 := h385c.2.2.2
              linarith only [hlam, p385_0]
          · linarith only [h0, h10, h13, h382, h384, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h13, h378, h379, h380, h382, h383, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · linarith only [h0, h13, h378, h382, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · linarith only [h13, h378, h379, hlam]

end R2N4
