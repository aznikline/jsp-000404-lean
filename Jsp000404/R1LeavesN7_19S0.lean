import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5556000 in
theorem r1l7_21_14_H_I_L_I_s4_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
            · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                · linarith only [h0, h13, h15, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h13, h14, h15, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h10, h14, h18, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h1bigk with h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h10, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h12, h13, h14, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h12, h13, h14, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h0, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h10, h12, h13, h14, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h0, h12, h13, h14, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h1, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h7, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h12, h13, h14, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h0, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h2, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h8, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h10, hlam, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h2, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p20_1]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h3, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h9, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h11, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [h12, hlam, p20_0]
                  · have p20_0 := h20c.1
                    have p20_1 := h20c.2.1
                    have p20_2 := h20c.2.2.1
                    have p20_3 := h20c.2.2.2
                    linarith only [hlam, p20_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
              · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                · rcases h1bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h10, h46, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h46, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    rcases p48_3 (m.d 0 1) (by simp) with h53 | h53
                    · rcases p48_3 (m.d 1 2) (by simp) with h54 | h54
                      · linarith only [h0, h54, hlam]
                      · linarith only [h54, h9, hlam]
                    · linarith only [h53, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h0, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h10, h13, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h0, h10, h13, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h0, h46, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h1, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h7, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h10, h13, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h0, h46, h7, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h2, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h8, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h10, hlam, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h2, h46, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h3, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h9, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h11, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h12, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [hlam, p48_0]
                · linarith only [h0, h13, h4, h46, h47, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                · linarith only [h0, h10, h46, h7, h79, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h10, h12, h13, h7, h79, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
            · rcases m.htr 2 4 5 (by decide) (by decide) with h83 | h83
              · linarith only [h0, h12, h8, h83, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h85 | h85
                · linarith only [h12, h8, h82, h85, hlam]
                · rcases h1bigk with h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p87_1]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h7, h82, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p87_1]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    rcases p87_3 (m.d 0 1) (by simp) with h91 | h91
                    · rcases p87_3 (m.d 1 2) (by simp) with h92 | h92
                      · linarith only [h0, h92, hlam]
                      · linarith only [h8, h92, hlam]
                    · linarith only [h91, hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    rcases p87_3 (m.d 0 1) (by simp) with h96 | h96
                    · rcases p87_3 (m.d 1 2) (by simp) with h97 | h97
                      · linarith only [h0, h97, hlam]
                      · linarith only [h9, h97, hlam]
                    · linarith only [h96, hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h0, hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h7, h82, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p87_1]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h0, h8, h82, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p87_1]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h0, h12, h8, h82, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p87_1]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h1, hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h7, hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h1, h8, h82, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p87_1]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h0, h12, h7, h8, h82, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p87_1]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h2, hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h8, hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h10, hlam, p87_1]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h12, hlam, p87_1]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h3, hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h9, hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h11, hlam, p87_0]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [h3, h8, h82, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p87_1]
                  · have p87_0 := h87c.1
                    have p87_1 := h87c.2.1
                    have p87_2 := h87c.2.2.1
                    have p87_3 := h87c.2.2.2
                    linarith only [hlam, p87_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
              · linarith only [h10, h12, h121, h82, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
                · linarith only [h10, h12, h123, hlam]
                · rcases h1bigk with h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [hlam, p125_0]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p125_1]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h10, h82, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p125_1]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h10, h82, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p125_1]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h10, h12, h82, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p125_1]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h0, hlam, p125_0]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [hlam, p125_0]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h10, h82, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p125_1]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p125_1]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p125_1]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h1, hlam, p125_0]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h7, hlam, p125_0]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [hlam, p125_0]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h1, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p125_1]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h0, h121, h7, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p125_1]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h2, hlam, p125_0]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h8, hlam, p125_0]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h10, hlam, p125_1]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [hlam, p125_0]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h12, hlam, p125_1]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h3, hlam, p125_0]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h9, hlam, p125_0]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h11, hlam, p125_0]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [h10, h82, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p125_1]
                  · have p125_0 := h125c.1
                    have p125_1 := h125c.2.1
                    have p125_2 := h125c.2.2.1
                    have p125_3 := h125c.2.2.2
                    linarith only [hlam, p125_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h151 | h151
          · linarith only [h10, h11, h151, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
            · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
              · linarith only [h0, h151, h154, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h156 | h156
                · linarith only [h11, h151, h153, h156, h7, hlam]
                · rcases h1bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [hlam, p158_0]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h153, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h153, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    rcases p158_3 (m.d 0 1) (by simp) with h162 | h162
                    · rcases p158_3 (m.d 1 2) (by simp) with h163 | h163
                      · linarith only [h0, h163, hlam]
                      · linarith only [h163, h8, hlam]
                    · linarith only [h162, hlam, p158_0]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h11, h153, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h0, hlam, p158_0]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [hlam, p158_0]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h153, h7, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p158_1]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h0, h153, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h0, h11, h153, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h1, hlam, p158_0]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h7, hlam, p158_0]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [hlam, p158_0]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h11, h153, h8, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p158_1]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h11, hlam, p158_1]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h2, hlam, p158_0]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h8, hlam, p158_0]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h10, hlam, p158_1]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [hlam, p158_0]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h151, hlam, p158_1]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h3, hlam, p158_0]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h9, hlam, p158_0]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p158_1]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [h0, h11, h153, h156, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1]
                  · have p158_0 := h158c.1
                    have p158_1 := h158c.2.1
                    have p158_2 := h158c.2.2.1
                    have p158_3 := h158c.2.2.2
                    linarith only [hlam, p158_0]
            · linarith only [h10, h11, h153, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h189 | h189
        · rcases m.htr 1 4 5 (by decide) (by decide) with h190 | h190
          · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
            · linarith only [h10, h191, h7, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h193 | h193
              · rcases m.htr 3 4 5 (by decide) (by decide) with h194 | h194
                · rcases h1bigk with h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p195_1]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h189, hc01, hc35, hlam, hphi, ht0b, ht5b, p195_1]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h10, h189, h194, hc01, hc45, hlam, hphi, ht0b, ht5b, p195_1]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    rcases p195_3 (m.d 0 1) (by simp) with h200 | h200
                    · rcases p195_3 (m.d 1 2) (by simp) with h201 | h201
                      · linarith only [h0, h201, hlam]
                      · linarith only [h201, h9, hlam]
                    · linarith only [h200, hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h0, hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h189, h194, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p195_1]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h0, h10, h189, h194, hc01, hc45, hlam, hphi, ht0b, ht5b, p195_1]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p195_1]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h1, hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h7, hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h10, hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h10, h9, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p195_1]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h2, hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h8, hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p195_1]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h1, h10, h189, h194, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p195_1]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h3, hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h9, hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h189, hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [h190, hlam, p195_0]
                  · have p195_0 := h195c.1
                    have p195_1 := h195c.2.1
                    have p195_2 := h195c.2.2.1
                    have p195_3 := h195c.2.2.2
                    linarith only [hlam, p195_0]
                · linarith only [h0, h10, h189, h194, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h226 | h226
                · linarith only [h10, h189, h191, h193, h226, hc23, hc34, hlam, hphi]
                · linarith only [h0, h10, h189, h226, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h10, h189, h190, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h230 | h230
          · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
            · linarith only [h0, h10, h231, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h233 | h233
              · rcases m.htr 3 4 5 (by decide) (by decide) with h234 | h234
                · rcases h1bigk with h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p235_1]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    rcases p235_3 (m.d 0 1) (by simp) with h238 | h238
                    · rcases p235_3 (m.d 1 2) (by simp) with h239 | h239
                      · linarith only [h0, h239, hlam]
                      · linarith only [h239, h7, hlam]
                    · linarith only [h238, hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h233, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p235_1]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    rcases p235_3 (m.d 0 1) (by simp) with h244 | h244
                    · rcases p235_3 (m.d 1 2) (by simp) with h245 | h245
                      · linarith only [h0, h245, hlam]
                      · linarith only [h245, h9, hlam]
                    · linarith only [h244, hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h0, hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p235_1]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h0, h233, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p235_1]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h0, h189, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p235_1]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h1, hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h7, hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h10, hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h189, hlam, p235_1]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h2, hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h8, hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h2, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p235_1]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h10, h189, h7, hc23, hc34, hlam, hphi, p235_1]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h3, hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h9, hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p235_1]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [h230, hlam, p235_0]
                  · have p235_0 := h235c.1
                    have p235_1 := h235c.2.1
                    have p235_2 := h235c.2.2.1
                    have p235_3 := h235c.2.2.2
                    linarith only [hlam, p235_0]
                · linarith only [h0, h10, h233, h234, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h270 | h270
                · rcases h1bigk with h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p271_1]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    rcases p271_3 (m.d 0 1) (by simp) with h274 | h274
                    · rcases p271_3 (m.d 1 2) (by simp) with h275 | h275
                      · linarith only [h0, h275, hlam]
                      · linarith only [h275, h7, hlam]
                    · linarith only [h274, hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h230, h231, h233, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p271_1]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h230, h231, h233, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p271_1]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h0, hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p271_1]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h0, h230, h231, h233, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p271_1]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p271_1]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h1, hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h7, hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h10, hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h189, hlam, p271_1]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h2, hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h8, hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h10, h7, hc23, hc34, hlam, hphi, p271_1]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h1, h10, h189, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p271_1]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h3, hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h9, hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p271_1]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [h230, hlam, p271_0]
                  · have p271_0 := h271c.1
                    have p271_1 := h271c.2.1
                    have p271_2 := h271c.2.2.1
                    have p271_3 := h271c.2.2.2
                    linarith only [hlam, p271_0]
                · linarith only [h10, h230, h270, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h302 | h302
            · linarith only [h10, h302, h7, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h304 | h304
              · linarith only [h0, h230, h304, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h306 | h306
                · rcases h1bigk with h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    rcases p307_3 (m.d 0 1) (by simp) with h310 | h310
                    · rcases p307_3 (m.d 1 2) (by simp) with h311 | h311
                      · linarith only [h0, h311, hlam]
                      · linarith only [h311, h7, hlam]
                    · linarith only [h310, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    rcases p307_3 (m.d 0 1) (by simp) with h315 | h315
                    · rcases p307_3 (m.d 1 2) (by simp) with h316 | h316
                      · linarith only [h0, h316, hlam]
                      · linarith only [h316, h8, hlam]
                    · linarith only [h315, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    rcases p307_3 (m.d 0 1) (by simp) with h320 | h320
                    · rcases p307_3 (m.d 1 2) (by simp) with h321 | h321
                      · linarith only [h0, h321, hlam]
                      · linarith only [h321, h9, hlam]
                    · linarith only [h320, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h0, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h0, h10, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h0, h10, h230, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h1, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h7, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h10, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h189, hlam, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h2, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h8, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h230, h306, h7, hc23, hc34, hlam, hphi, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h230, hlam, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h3, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h9, hlam, p307_0]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [h1, h230, h306, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p307_1]
                  · have p307_0 := h307c.1
                    have p307_1 := h307c.2.1
                    have p307_2 := h307c.2.2.1
                    have p307_3 := h307c.2.2.2
                    linarith only [hlam, p307_0]
                · rcases h1bigk with h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p345_1]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    rcases p345_3 (m.d 0 1) (by simp) with h348 | h348
                    · rcases p345_3 (m.d 1 2) (by simp) with h349 | h349
                      · linarith only [h0, h349, hlam]
                      · linarith only [h349, h7, hlam]
                    · linarith only [h348, hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    rcases p345_3 (m.d 0 1) (by simp) with h353 | h353
                    · rcases p345_3 (m.d 1 2) (by simp) with h354 | h354
                      · linarith only [h0, h354, hlam]
                      · linarith only [h354, h8, hlam]
                    · linarith only [h353, hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    rcases p345_3 (m.d 0 1) (by simp) with h358 | h358
                    · rcases p345_3 (m.d 1 2) (by simp) with h359 | h359
                      · linarith only [h0, h359, hlam]
                      · linarith only [h359, h9, hlam]
                    · linarith only [h358, hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h0, hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p345_1]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h0, h302, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p345_1]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p345_1]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h1, hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h7, hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h10, hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h189, hlam, p345_1]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h2, hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h8, hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h2, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p345_1]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h230, hlam, p345_1]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h3, hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h9, hlam, p345_0]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p345_1]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [h0, h189, h306, h4, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p345_1]
                  · have p345_0 := h345c.1
                    have p345_1 := h345c.2.1
                    have p345_2 := h345c.2.2.1
                    have p345_3 := h345c.2.2.2
                    linarith only [hlam, p345_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h383 | h383
      · rcases m.htr 1 3 5 (by decide) (by decide) with h384 | h384
        · linarith only [h384, h7, h9, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h386 | h386
          · linarith only [h386, h8, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h388 | h388
            · rcases m.htr 2 4 5 (by decide) (by decide) with h389 | h389
              · linarith only [h0, h386, h388, h389, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h388, h389, h7, h9, hc34, hc45, hlam, hphi]
            · linarith only [h383, h384, h388, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h393 | h393
        · linarith only [h393, h7, h9, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h395 | h395
          · linarith only [h395, h8, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h397 | h397
            · linarith only [h0, h383, h395, h397, h4, h6, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h399 | h399
              · linarith only [h395, h399, h8, h9, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h401 | h401
                · linarith only [h1, h399, h401, h5, h8, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h1bigk with h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h397, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p403_1]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    rcases p403_3 (m.d 0 1) (by simp) with h406 | h406
                    · rcases p403_3 (m.d 1 2) (by simp) with h407 | h407
                      · linarith only [h0, h407, hlam]
                      · linarith only [h407, h7, hlam]
                    · linarith only [h406, hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    rcases p403_3 (m.d 0 1) (by simp) with h411 | h411
                    · rcases p403_3 (m.d 1 2) (by simp) with h412 | h412
                      · linarith only [h0, h412, hlam]
                      · linarith only [h412, h8, hlam]
                    · linarith only [h411, hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h397, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p403_1]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h0, hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h399, h4, h6, h7, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p403_1]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h0, h399, h4, h6, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p403_1]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h9, hlam, p403_1]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h1, hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h7, hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h383, hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h393, hlam, p403_1]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h2, hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h8, hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h2, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p403_1]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h395, hlam, p403_1]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h3, hlam, p403_0]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h7, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p403_1]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h0, h399, h4, h6, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p403_1]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [h0, h399, h4, h6, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p403_1]
                  · have p403_0 := h403c.1
                    have p403_1 := h403c.2.1
                    have p403_2 := h403c.2.2.1
                    have p403_3 := h403c.2.2.2
                    linarith only [hlam, p403_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h437 | h437
    · rcases m.htr 1 3 4 (by decide) (by decide) with h438 | h438
      · linarith only [h438, h7, h8, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h440 | h440
        · rcases m.htr 1 4 5 (by decide) (by decide) with h441 | h441
          · rcases m.htr 2 3 4 (by decide) (by decide) with h442 | h442
            · linarith only [h438, h442, h7, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h444 | h444
              · rcases m.htr 3 4 5 (by decide) (by decide) with h445 | h445
                · rcases h1bigk with h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p446_1]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h440, h445, hc01, hc45, hlam, hphi, ht0b, ht5b, p446_1]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p446_1]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    rcases p446_3 (m.d 0 1) (by simp) with h451 | h451
                    · rcases p446_3 (m.d 1 2) (by simp) with h452 | h452
                      · linarith only [h0, h452, hlam]
                      · linarith only [h437, h452, hlam]
                    · linarith only [h451, hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h0, hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h440, h445, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p446_1]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h8, hlam, p446_1]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h1, h442, h5, h8, hc01, hc15, hlam, hphi, ht0b, ht5b, p446_1]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h1, hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h7, hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h438, hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h1, h437, hc01, hc25, hlam, hphi, ht0b, ht5b, p446_1]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h2, hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h1, h442, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p446_1]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h1, h442, h5, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p446_1]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h1, h440, h442, h445, h5, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p446_1]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h3, hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h437, hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h440, hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [h441, hlam, p446_0]
                  · have p446_0 := h446c.1
                    have p446_1 := h446c.2.1
                    have p446_2 := h446c.2.2.1
                    have p446_3 := h446c.2.2.2
                    linarith only [hlam, p446_0]
                · linarith only [h0, h4, h442, h445, h6, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h444, h7, h8, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h440, h441, h7, h8, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h479 | h479
          · rcases m.htr 2 3 4 (by decide) (by decide) with h480 | h480
            · linarith only [h0, h4, h480, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h482 | h482
              · rcases m.htr 3 4 5 (by decide) (by decide) with h483 | h483
                · rcases h1bigk with h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p484_1]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    rcases p484_3 (m.d 0 1) (by simp) with h487 | h487
                    · rcases p484_3 (m.d 1 2) (by simp) with h488 | h488
                      · linarith only [h0, h488, hlam]
                      · linarith only [h488, h7, hlam]
                    · linarith only [h487, hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p484_1]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    rcases p484_3 (m.d 0 1) (by simp) with h493 | h493
                    · rcases p484_3 (m.d 1 2) (by simp) with h494 | h494
                      · linarith only [h0, h494, hlam]
                      · linarith only [h437, h494, hlam]
                    · linarith only [h493, hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h0, hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h7, h8, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p484_1]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h8, hlam, p484_1]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h1, h440, h480, h5, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p484_1]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h1, hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h7, hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h438, hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h440, hlam, p484_1]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h2, hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h437, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p484_1]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h1, h480, h5, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p484_1]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h1, h440, h480, h5, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p484_1]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h3, hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h437, hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p484_1]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [h479, hlam, p484_0]
                  · have p484_0 := h484c.1
                    have p484_1 := h484c.2.1
                    have p484_2 := h484c.2.2.1
                    have p484_3 := h484c.2.2.2
                    linarith only [hlam, p484_0]
                · linarith only [h0, h4, h480, h483, h6, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h437, h479, h482, h8, hlam]
          · linarith only [h437, h479, h8, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h521 | h521
      · linarith only [h521, h7, h8, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h523 | h523
        · linarith only [h437, h523, h7, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h525 | h525
          · rcases m.htr 2 3 4 (by decide) (by decide) with h526 | h526
            · linarith only [h521, h526, h7, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h528 | h528
              · rcases m.htr 3 4 5 (by decide) (by decide) with h529 | h529
                · rcases h1bigk with h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [hlam, p530_0]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p530_1]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    rcases p530_3 (m.d 0 1) (by simp) with h533 | h533
                    · rcases p530_3 (m.d 1 2) (by simp) with h534 | h534
                      · linarith only [h0, h534, hlam]
                      · linarith only [h534, h7, hlam]
                    · linarith only [h533, hlam, p530_0]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h437, h525, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p530_1]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h437, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p530_1]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h0, hlam, p530_0]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [hlam, p530_0]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h437, h523, h7, hc23, hc35, hlam, hphi, p530_1]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h8, hlam, p530_1]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h437, hlam, p530_1]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h1, hlam, p530_0]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h7, hlam, p530_0]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [hlam, p530_0]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h521, hlam, p530_0]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h523, hlam, p530_1]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h2, hlam, p530_0]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h1, h5, h526, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p530_1]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h1, h5, h526, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p530_1]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [hlam, p530_0]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h1, h5, h526, h8, hc01, hc15, hlam, hphi, ht0b, ht5b, p530_1]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h3, hlam, p530_0]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h7, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p530_1]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h1, h437, h5, h526, h528, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p530_1]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [h525, hlam, p530_0]
                  · have p530_0 := h530c.1
                    have p530_1 := h530c.2.1
                    have p530_2 := h530c.2.2.1
                    have p530_3 := h530c.2.2.2
                    linarith only [hlam, p530_0]
                · linarith only [h525, h526, h529, h8, hlam]
              · linarith only [h525, h528, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h562 | h562
            · linarith only [h0, h4, h562, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h564 | h564
              · linarith only [h1, h5, h525, h562, h564, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h4, h564, h6, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

end R2N4
