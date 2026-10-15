import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
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
                linarith only [h10, hlam, p24_0]
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
                linarith only [h11, hlam, p24_0]
              · have p24_0 := h24c.1
                have p24_1 := h24c.2.1
                have p24_2 := h24c.2.2.1
                have p24_3 := h24c.2.2.2
                linarith only [h13, hlam, p24_1]
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
                linarith only [h12, hlam, p24_0]
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
                linarith only [h10, hlam, p59_0]
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
                linarith only [h11, hlam, p59_0]
              · have p59_0 := h59c.1
                have p59_1 := h59c.2.1
                have p59_2 := h59c.2.2.1
                have p59_3 := h59c.2.2.2
                linarith only [h13, hlam, p59_1]
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
                linarith only [h12, hlam, p59_0]
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
                linarith only [h10, hlam, p103_0]
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
                        · rcases h1emax with h159 | h159 | h159 | h159 | h159
                          · linarith only [h0, h10, h15, h159, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p103_1]
                          · linarith only [h10, h11, h15, h159, h97, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p103_1]
                          · linarith only [h11, h15, h159, h97, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p103_1]
                          · rcases h2bigk with h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h0, h10, h11, h15, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p103_1, p163_1]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              rcases p163_3 (m.d 0 2) (by simp) with h166 | h166
                              · rcases p163_3 (m.d 1 2) (by simp) with h167 | h167
                                · linarith only [h0, h167, hlam]
                                · linarith only [h10, h167, hlam]
                              · linarith only [h166, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              rcases p163_3 (m.d 0 2) (by simp) with h171 | h171
                              · rcases p163_3 (m.d 1 2) (by simp) with h172 | h172
                                · linarith only [h0, h172, hlam]
                                · linarith only [h11, h172, hlam]
                              · linarith only [h171, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              rcases p163_3 (m.d 0 2) (by simp) with h176 | h176
                              · rcases p163_3 (m.d 1 2) (by simp) with h177 | h177
                                · linarith only [h0, h177, hlam]
                                · linarith only [h12, h177, hlam]
                              · linarith only [h176, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h0, hlam, p163_1]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h0, h101, h98, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p163_1]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              rcases p163_3 (m.d 0 2) (by simp) with h184 | h184
                              · rcases p163_3 (m.d 1 2) (by simp) with h185 | h185
                                · rcases p163_3 (m.d 2 3) (by simp) with h186 | h186
                                  · linarith only [h10, h186, hlam]
                                  · linarith only [h186, h97, hlam]
                                · linarith only [h185, hlam, p163_0]
                              · linarith only [h184, h5, hlam]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              rcases p163_3 (m.d 0 2) (by simp) with h191 | h191
                              · rcases p163_3 (m.d 1 2) (by simp) with h192 | h192
                                · rcases p163_3 (m.d 2 3) (by simp) with h193 | h193
                                  · linarith only [h10, h193, hlam]
                                  · linarith only [h193, h98, hlam]
                                · linarith only [h192, hlam, p163_0]
                              · linarith only [h191, h6, hlam]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h4, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h10, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h0, h10, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p163_1]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h0, h10, h97, h99, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p163_1]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h5, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h11, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h97, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h99, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h6, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h12, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h98, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h0, h12, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p163_1]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [hlam, p163_0]
                          · rcases h2bigk with h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h0, h10, h11, h15, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p103_1, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              rcases p213_3 (m.d 0 2) (by simp) with h216 | h216
                              · rcases p213_3 (m.d 1 2) (by simp) with h217 | h217
                                · linarith only [h0, h217, hlam]
                                · linarith only [h10, h217, hlam]
                              · linarith only [h216, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              rcases p213_3 (m.d 0 2) (by simp) with h221 | h221
                              · rcases p213_3 (m.d 1 2) (by simp) with h222 | h222
                                · linarith only [h0, h222, hlam]
                                · linarith only [h11, h222, hlam]
                              · linarith only [h221, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              rcases p213_3 (m.d 0 2) (by simp) with h226 | h226
                              · rcases p213_3 (m.d 1 2) (by simp) with h227 | h227
                                · linarith only [h0, h227, hlam]
                                · linarith only [h12, h227, hlam]
                              · linarith only [h226, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h0, hlam, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h0, h101, h98, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              rcases p213_3 (m.d 0 2) (by simp) with h234 | h234
                              · rcases p213_3 (m.d 1 2) (by simp) with h235 | h235
                                · rcases p213_3 (m.d 2 3) (by simp) with h236 | h236
                                  · linarith only [h10, h236, hlam]
                                  · linarith only [h236, h97, hlam]
                                · linarith only [h235, hlam, p213_0]
                              · linarith only [h234, h5, hlam]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              rcases p213_3 (m.d 0 2) (by simp) with h241 | h241
                              · rcases p213_3 (m.d 1 2) (by simp) with h242 | h242
                                · rcases p213_3 (m.d 2 3) (by simp) with h243 | h243
                                  · linarith only [h10, h243, hlam]
                                  · linarith only [h243, h98, hlam]
                                · linarith only [h242, hlam, p213_0]
                              · linarith only [h241, h6, hlam]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h4, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h10, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h0, h10, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h5, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h11, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h97, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h99, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h6, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h12, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h98, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h0, h12, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [hlam, p213_0]
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
                linarith only [h11, hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h13, hlam, p103_1]
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
                linarith only [h12, hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [h14, hlam, p103_0]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                rcases p103_3 (m.d 0 1) (by simp) with h274 | h274
                · rcases p103_3 (m.d 1 2) (by simp) with h275 | h275
                  · rcases p103_3 (m.d 1 3) (by simp) with h276 | h276
                    · rcases p103_3 (m.d 1 4) (by simp) with h277 | h277
                      · linarith only [h15, h277, hlam]
                      · rcases p103_3 (m.d 1 5) (by simp) with h279 | h279
                        · rcases h1emax with h280 | h280 | h280 | h280 | h280
                          · linarith only [h0, h10, h280, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h10, h11, h14, h280, h97, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p103_1]
                          · linarith only [h11, h14, h280, h97, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p103_1]
                          · rcases h2bigk with h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h0, h10, h11, h14, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p103_1, p284_1]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              rcases p284_3 (m.d 0 2) (by simp) with h287 | h287
                              · rcases p284_3 (m.d 1 2) (by simp) with h288 | h288
                                · linarith only [h0, h288, hlam]
                                · linarith only [h10, h288, hlam]
                              · linarith only [h287, hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h11, h15, h4, h7, h9, hlam, p103_1, p284_2]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              rcases p284_3 (m.d 0 2) (by simp) with h293 | h293
                              · rcases p284_3 (m.d 1 2) (by simp) with h294 | h294
                                · linarith only [h0, h294, hlam]
                                · linarith only [h12, h294, hlam]
                              · linarith only [h293, hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h0, hlam, p284_1]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h0, h101, h98, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p284_1]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              rcases p284_3 (m.d 0 2) (by simp) with h301 | h301
                              · rcases p284_3 (m.d 1 2) (by simp) with h302 | h302
                                · rcases p284_3 (m.d 2 3) (by simp) with h303 | h303
                                  · linarith only [h10, h303, hlam]
                                  · linarith only [h303, h97, hlam]
                                · linarith only [h302, hlam, p284_0]
                              · linarith only [h301, h5, hlam]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              rcases p284_3 (m.d 0 2) (by simp) with h308 | h308
                              · rcases p284_3 (m.d 1 2) (by simp) with h309 | h309
                                · rcases p284_3 (m.d 2 3) (by simp) with h310 | h310
                                  · linarith only [h10, h310, hlam]
                                  · linarith only [h310, h98, hlam]
                                · linarith only [h309, hlam, p284_0]
                              · linarith only [h308, h6, hlam]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h4, hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h10, hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h0, h10, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p284_1]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p284_1]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h5, hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h11, hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h97, hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h99, hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h6, hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h12, hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h98, hlam, p284_0]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [h0, h12, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p284_1]
                            · have p284_0 := h284c.1
                              have p284_1 := h284c.2.1
                              have p284_2 := h284c.2.2.1
                              have p284_3 := h284c.2.2.2
                              linarith only [hlam, p284_0]
                          · linarith only [h11, h280, h97, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p103_1]
                        · linarith only [h15, h279, hlam]
                    · linarith only [h13, h276, hlam]
                  · linarith only [h11, h275, hlam]
                · linarith only [h2, h274, hlam]
              · have p103_0 := h103c.1
                have p103_1 := h103c.2.1
                have p103_2 := h103c.2.2.1
                have p103_3 := h103c.2.2.2
                linarith only [hlam, p103_0]
        · linarith only [h0, h10, h14, h97, h98, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h337 | h337
        · linarith only [h0, h10, h13, h337, h97, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h339 | h339
          · linarith only [h13, h15, h339, h97, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h341 | h341
            · linarith only [h13, h15, h341, hlam]
            · rcases h1bigk with h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h10, h13, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h13, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                rcases p343_3 (m.d 0 1) (by simp) with h347 | h347
                · rcases p343_3 (m.d 1 2) (by simp) with h348 | h348
                  · linarith only [h0, h348, hlam]
                  · linarith only [h11, h348, hlam]
                · linarith only [h347, hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                rcases p343_3 (m.d 0 1) (by simp) with h352 | h352
                · rcases p343_3 (m.d 1 2) (by simp) with h353 | h353
                  · linarith only [h0, h353, hlam]
                  · linarith only [h12, h353, hlam]
                · linarith only [h352, hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h0, hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h14, h341, h97, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p343_1]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h0, h13, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h0, h14, h341, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h1, hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h10, hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h1, h13, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h0, h10, h14, h341, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h2, hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h11, hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h13, hlam, p343_1]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h15, hlam, p343_1]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h3, hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h12, hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h14, hlam, p343_0]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [h13, h3, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1]
              · have p343_0 := h343c.1
                have p343_1 := h343c.2.1
                have p343_2 := h343c.2.2.1
                have p343_3 := h343c.2.2.2
                linarith only [hlam, p343_0]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h377 | h377
    · linarith only [h13, h14, h377, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h379 | h379
      · rcases m.htr 2 3 5 (by decide) (by decide) with h380 | h380
        · linarith only [h10, h14, h380, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h382 | h382
          · linarith only [h11, h377, h382, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h384 | h384
            · linarith only [h10, h11, h14, h377, h379, h384, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · rcases h1bigk with h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h10, h379, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p386_1]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                rcases p386_3 (m.d 0 1) (by simp) with h389 | h389
                · rcases p386_3 (m.d 1 2) (by simp) with h390 | h390
                  · linarith only [h0, h390, hlam]
                  · linarith only [h10, h390, hlam]
                · linarith only [h389, hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                rcases p386_3 (m.d 0 1) (by simp) with h394 | h394
                · rcases p386_3 (m.d 1 2) (by simp) with h395 | h395
                  · linarith only [h0, h395, hlam]
                  · linarith only [h11, h395, hlam]
                · linarith only [h394, hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                rcases p386_3 (m.d 0 1) (by simp) with h399 | h399
                · rcases p386_3 (m.d 1 2) (by simp) with h400 | h400
                  · linarith only [h0, h400, hlam]
                  · linarith only [h12, h400, hlam]
                · linarith only [h399, hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h0, hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h0, h10, h379, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p386_1]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                rcases p386_3 (m.d 0 1) (by simp) with h407 | h407
                · rcases p386_3 (m.d 1 2) (by simp) with h408 | h408
                  · rcases p386_3 (m.d 1 3) (by simp) with h409 | h409
                    · linarith only [h10, h409, hlam]
                    · linarith only [h13, h409, hlam]
                  · linarith only [h11, h408, hlam]
                · linarith only [h2, h407, hlam]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h0, h10, h14, h379, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p386_1]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h1, hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h10, hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h0, h11, h14, h379, h384, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p386_1]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h14, hlam, p386_1]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h2, hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h11, hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h13, hlam, p386_1]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h377, hlam, p386_1]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h3, hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h12, hlam, p386_0]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [h10, h3, h379, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p386_1]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                rcases p386_3 (m.d 0 1) (by simp) with h428 | h428
                · rcases p386_3 (m.d 1 2) (by simp) with h429 | h429
                  · rcases p386_3 (m.d 1 3) (by simp) with h430 | h430
                    · linarith only [h14, h430, hlam]
                    · linarith only [h13, h430, hlam]
                  · linarith only [h11, h429, hlam]
                · linarith only [h2, h428, hlam]
              · have p386_0 := h386c.1
                have p386_1 := h386c.2.1
                have p386_2 := h386c.2.2.1
                have p386_3 := h386c.2.2.2
                linarith only [hlam, p386_0]
      · linarith only [h13, h14, h379, hc23, hc35, hlam, hphi]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  rcases m.htr 1 4 5 (by decide) (by decide) with h438 | h438
  · rcases m.htr 2 3 4 (by decide) (by decide) with h439 | h439
    · linarith only [h0, h13, h4, h437, h439, hc01, hc35, hlam, hphi, ht0b, ht5b]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h441 | h441
      · rcases m.htr 2 4 5 (by decide) (by decide) with h442 | h442
        · rcases m.htr 3 4 5 (by decide) (by decide) with h443 | h443
          · rcases h1bigk with h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h10, h441, h443, hc01, hc45, hlam, hphi, ht0b, ht5b, p444_1]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              rcases p444_3 (m.d 0 1) (by simp) with h447 | h447
              · rcases p444_3 (m.d 1 2) (by simp) with h448 | h448
                · linarith only [h0, h448, hlam]
                · linarith only [h10, h448, hlam]
              · linarith only [h447, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              rcases p444_3 (m.d 0 1) (by simp) with h452 | h452
              · rcases p444_3 (m.d 1 2) (by simp) with h453 | h453
                · linarith only [h0, h453, hlam]
                · linarith only [h11, h453, hlam]
              · linarith only [h452, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              rcases p444_3 (m.d 0 1) (by simp) with h457 | h457
              · rcases p444_3 (m.d 1 2) (by simp) with h458 | h458
                · linarith only [h0, h458, hlam]
                · linarith only [h12, h458, hlam]
              · linarith only [h457, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h0, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h0, h10, h441, h443, hc01, hc45, hlam, hphi, ht0b, ht5b, p444_1]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h0, h10, h13, h441, h443, hc01, hc45, hlam, hphi, ht0b, ht5b, p444_1]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              rcases p444_3 (m.d 0 1) (by simp) with h466 | h466
              · rcases p444_3 (m.d 1 2) (by simp) with h467 | h467
                · rcases p444_3 (m.d 1 3) (by simp) with h468 | h468
                  · linarith only [h10, h468, hlam]
                  · linarith only [h437, h468, hlam]
                · linarith only [h12, h467, hlam]
              · linarith only [h3, h466, hlam]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h1, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h10, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h13, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h0, h12, h13, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p444_1]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h2, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h11, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h10, h2, h441, h443, hc01, hc45, hlam, hphi, ht0b, ht5b, p444_1]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              rcases p444_3 (m.d 0 1) (by simp) with h482 | h482
              · rcases p444_3 (m.d 1 2) (by simp) with h483 | h483
                · rcases p444_3 (m.d 1 3) (by simp) with h484 | h484
                  · linarith only [h13, h484, hlam]
                  · linarith only [h437, h484, hlam]
                · linarith only [h12, h483, hlam]
              · linarith only [h3, h482, hlam]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h3, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h12, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h437, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [h438, hlam, p444_0]
            · have p444_0 := h444c.1
              have p444_1 := h444c.2.1
              have p444_2 := h444c.2.2.1
              have p444_3 := h444c.2.2.2
              linarith only [hlam, p444_0]
          · linarith only [h0, h10, h13, h4, h441, h443, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h2, h438, h439, h441, h442, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · linarith only [h0, h13, h4, h437, h441, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · linarith only [h13, h437, h438, hlam]

end R2N4
