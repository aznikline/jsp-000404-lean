import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6988000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s6_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
      · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
        · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
          · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
            · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
              · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h10, h15, h18, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h10, h15, h17, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                · linarith only [h0, h10, h13, h17, h21, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h0bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h16, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h0, hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h15, h17, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h0, h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h0, h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h1, hlam, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h4, hlam, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h15, h17, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h0, h15, h17, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h2, hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h5, hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h7, hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h0, h15, h17, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h3, hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h6, hlam, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h8, hlam, p23_0]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [h9, hlam, p23_1]
                  · have p23_0 := h23c.1
                    have p23_1 := h23c.2.1
                    have p23_2 := h23c.2.2.1
                    have p23_3 := h23c.2.2.2
                    linarith only [hlam, p23_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
              · linarith only [h15, h16, h49, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h51 | h51
                · linarith only [h15, h16, h49, h51, h8, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h10, h13, h14, h15, h16, h51, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
            · linarith only [h0, h10, h13, h15, h54, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
              · rcases m.htr 3 4 5 (by decide) (by decide) with h57 | h57
                · rcases h0bigk with h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h0, h10, h13, h54, h57, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h1, h13, h54, h57, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h54, h57, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h54, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h0, hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h1, h13, h54, h57, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h0, h54, h57, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h0, h54, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h1, hlam, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h4, hlam, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h54, h57, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h0, h4, h54, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h2, hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h5, hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h7, hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h54, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h3, hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h6, hlam, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h8, hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h9, hlam, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [hlam, p58_0]
                · linarith only [h0, h10, h13, h14, h15, h57, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h85 | h85
                · linarith only [h0, h10, h13, h56, h85, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h10, h13, h14, h15, h85, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
          · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
            · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
              · linarith only [h0, h11, h14, h90, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
                · linarith only [h11, h14, h88, h92, hlam]
                · rcases h0bigk with h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [hlam, p94_0]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h4, h89, h92, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h4, h89, h92, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h11, h14, h88, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h11, h14, h88, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h0, hlam, p94_0]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [hlam, p94_0]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h11, h14, h8, h88, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h0, h11, h14, h88, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h0, h11, h14, h88, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h1, hlam, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h4, hlam, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [hlam, p94_0]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h11, h14, h88, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h0, h11, h14, h4, h88, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h2, hlam, p94_0]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h5, hlam, p94_0]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h7, hlam, p94_0]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [hlam, p94_0]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h11, h14, h88, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h3, hlam, p94_0]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h6, hlam, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h8, hlam, p94_0]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [h9, hlam, p94_1]
                  · have p94_0 := h94c.1
                    have p94_1 := h94c.2.1
                    have p94_2 := h94c.2.2.1
                    have p94_3 := h94c.2.2.2
                    linarith only [hlam, p94_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h120 | h120
              · linarith only [h11, h120, h14, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                · linarith only [h0, h10, h122, h13, h14, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h0bigk with h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h122, h4, h7, h89, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h122, h7, h89, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h122, h89, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h8, h89, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h0, hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h122, h7, h89, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h0, h122, h89, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h0, h8, h89, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h1, hlam, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h4, hlam, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h122, h89, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h0, h4, h8, h89, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h2, hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h5, hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h7, hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h8, h89, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h3, hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h6, hlam, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h8, hlam, p124_0]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [h9, hlam, p124_1]
                  · have p124_0 := h124c.1
                    have p124_1 := h124c.2.1
                    have p124_2 := h124c.2.2.1
                    have p124_3 := h124c.2.2.2
                    linarith only [hlam, p124_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h150 | h150
            · linarith only [h0, h10, h13, h150, h88, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h152 | h152
              · linarith only [h13, h14, h152, h88, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h154 | h154
                · linarith only [h13, h14, h154, hlam]
                · rcases h0bigk with h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [hlam, p156_0]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h13, h14, h4, h7, h88, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h13, h14, h7, h88, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h13, h14, h88, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h13, h14, h88, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
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
                    linarith only [h13, h14, h7, h88, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h0, h13, h14, h88, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h0, h13, h14, h88, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h1, hlam, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h4, hlam, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [hlam, p156_0]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h13, h14, h88, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h0, h13, h14, h4, h88, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h2, hlam, p156_0]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h5, hlam, p156_0]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h7, hlam, p156_0]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [hlam, p156_0]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h13, h14, h88, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h3, hlam, p156_0]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h6, hlam, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h8, hlam, p156_0]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [h9, hlam, p156_1]
                  · have p156_0 := h156c.1
                    have p156_1 := h156c.2.1
                    have p156_2 := h156c.2.2.1
                    have p156_3 := h156c.2.2.2
                    linarith only [hlam, p156_0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
        · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
          · linarith only [h0, h10, h13, h183, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
            · rcases m.htr 2 4 5 (by decide) (by decide) with h186 | h186
              · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                · rcases h0bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [hlam, p188_0]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h1, h10, h185, h187, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p188_1]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h1, h10, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p188_1]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h183, h185, h187, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p188_1]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    rcases p188_3 (m.d 0 1) (by simp) with h193 | h193
                    · rcases p188_3 (m.d 0 2) (by simp) with h194 | h194
                      · linarith only [h0, h194, hlam]
                      · linarith only [h194, h6, hlam]
                    · linarith only [h193, h3, hlam]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h0, hlam, p188_0]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [hlam, p188_0]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h10, h13, h185, h187, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p188_1]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h0, h10, h13, h185, h187, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p188_1]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    rcases p188_3 (m.d 0 1) (by simp) with h202 | h202
                    · rcases p188_3 (m.d 0 2) (by simp) with h203 | h203
                      · rcases p188_3 (m.d 0 3) (by simp) with h204 | h204
                        · linarith only [h204, h4, hlam]
                        · linarith only [h204, h8, hlam]
                      · linarith only [h203, h6, hlam]
                    · linarith only [h202, h3, hlam]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h1, hlam, p188_1]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h4, hlam, p188_1]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [hlam, p188_0]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h10, h13, h185, h187, h7, hc03, hc45, hlam, hphi, ht0b, ht5b, p188_1]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    rcases p188_3 (m.d 0 1) (by simp) with h213 | h213
                    · rcases p188_3 (m.d 0 2) (by simp) with h214 | h214
                      · rcases p188_3 (m.d 0 3) (by simp) with h215 | h215
                        · rcases p188_3 (m.d 0 4) (by simp) with h216 | h216
                          · linarith only [h216, h7, hlam]
                          · linarith only [h216, h9, hlam]
                        · linarith only [h215, h8, hlam]
                      · linarith only [h214, h6, hlam]
                    · linarith only [h213, h3, hlam]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h2, hlam, p188_0]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h5, hlam, p188_0]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h7, hlam, p188_0]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [hlam, p188_0]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    rcases p188_3 (m.d 0 1) (by simp) with h226 | h226
                    · rcases p188_3 (m.d 0 2) (by simp) with h227 | h227
                      · rcases p188_3 (m.d 0 3) (by simp) with h228 | h228
                        · rcases p188_3 (m.d 0 4) (by simp) with h229 | h229
                          · rcases p188_3 (m.d 0 5) (by simp) with h230 | h230
                            · linarith only [h230, h9, hlam]
                            · rcases h0emin with h232 | h232 | h232 | h232 | h232
                              · rcases h2bigk with h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h0, h10, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p233_1]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  rcases p233_3 (m.d 0 2) (by simp) with h236 | h236
                                  · rcases p233_3 (m.d 1 2) (by simp) with h237 | h237
                                    · linarith only [h0, h237, hlam]
                                    · linarith only [h10, h237, hlam]
                                  · linarith only [h236, hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  rcases p233_3 (m.d 0 2) (by simp) with h241 | h241
                                  · rcases p233_3 (m.d 1 2) (by simp) with h242 | h242
                                    · linarith only [h0, h242, hlam]
                                    · linarith only [h11, h242, hlam]
                                  · linarith only [h241, hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h4, h6, h7, hlam, p188_1, p233_2]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h0, hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h0, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p233_1]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h0, h183, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p233_1]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  rcases p233_3 (m.d 0 2) (by simp) with h251 | h251
                                  · rcases p233_3 (m.d 1 2) (by simp) with h252 | h252
                                    · rcases p233_3 (m.d 2 3) (by simp) with h253 | h253
                                      · linarith only [h10, h253, hlam]
                                      · linarith only [h185, h253, hlam]
                                    · linarith only [h252, hlam, p233_0]
                                  · linarith only [h251, h6, hlam]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h4, hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h10, hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h183, hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h0, h10, h13, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p233_1]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h5, hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h11, hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p233_1]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h0, h11, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p233_1]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h6, hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h12, hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h185, hlam, p233_1]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [h186, hlam, p233_0]
                                · have p233_0 := h233c.1
                                  have p233_1 := h233c.2.1
                                  have p233_2 := h233c.2.2.1
                                  have p233_3 := h233c.2.2.2
                                  linarith only [hlam, p233_0]
                              · rcases h2bigk with h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h0, h10, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p273_1]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  rcases p273_3 (m.d 0 2) (by simp) with h276 | h276
                                  · rcases p273_3 (m.d 1 2) (by simp) with h277 | h277
                                    · linarith only [h0, h277, hlam]
                                    · linarith only [h10, h277, hlam]
                                  · linarith only [h276, hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  rcases p273_3 (m.d 0 2) (by simp) with h281 | h281
                                  · rcases p273_3 (m.d 1 2) (by simp) with h282 | h282
                                    · linarith only [h0, h282, hlam]
                                    · linarith only [h11, h282, hlam]
                                  · linarith only [h281, hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h4, h6, h7, hlam, p188_1, p273_2]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h0, hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h0, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p273_1]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h0, h183, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p273_1]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  rcases p273_3 (m.d 0 2) (by simp) with h291 | h291
                                  · rcases p273_3 (m.d 1 2) (by simp) with h292 | h292
                                    · rcases p273_3 (m.d 2 3) (by simp) with h293 | h293
                                      · linarith only [h10, h293, hlam]
                                      · linarith only [h185, h293, hlam]
                                    · linarith only [h292, hlam, p273_0]
                                  · linarith only [h291, h6, hlam]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h4, hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h10, hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h183, hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p273_1]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h5, hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h11, hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p273_1]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h0, h11, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p273_1]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h6, hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h12, hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h185, hlam, p273_1]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [h186, hlam, p273_0]
                                · have p273_0 := h273c.1
                                  have p273_1 := h273c.2.1
                                  have p273_2 := h273c.2.2.1
                                  have p273_3 := h273c.2.2.2
                                  linarith only [hlam, p273_0]
                              · rcases h2bigk with h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h0, h10, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  rcases p313_3 (m.d 0 2) (by simp) with h316 | h316
                                  · rcases p313_3 (m.d 1 2) (by simp) with h317 | h317
                                    · linarith only [h0, h317, hlam]
                                    · linarith only [h10, h317, hlam]
                                  · linarith only [h316, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  rcases p313_3 (m.d 0 2) (by simp) with h321 | h321
                                  · rcases p313_3 (m.d 1 2) (by simp) with h322 | h322
                                    · linarith only [h0, h322, hlam]
                                    · linarith only [h11, h322, hlam]
                                  · linarith only [h321, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h4, h6, h7, hlam, p188_1, p313_2]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h0, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h0, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h0, h183, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  rcases p313_3 (m.d 0 2) (by simp) with h331 | h331
                                  · rcases p313_3 (m.d 1 2) (by simp) with h332 | h332
                                    · rcases p313_3 (m.d 2 3) (by simp) with h333 | h333
                                      · linarith only [h10, h333, hlam]
                                      · linarith only [h185, h333, hlam]
                                    · linarith only [h332, hlam, p313_0]
                                  · linarith only [h331, h6, hlam]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h4, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h10, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h183, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h5, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h11, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h0, h11, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h6, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h12, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h185, hlam, p313_1]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [h186, hlam, p313_0]
                                · have p313_0 := h313c.1
                                  have p313_1 := h313c.2.1
                                  have p313_2 := h313c.2.2.1
                                  have p313_3 := h313c.2.2.2
                                  linarith only [hlam, p313_0]
                              · rcases h2bigk with h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h0, h10, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p353_1]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  rcases p353_3 (m.d 0 2) (by simp) with h356 | h356
                                  · rcases p353_3 (m.d 1 2) (by simp) with h357 | h357
                                    · linarith only [h0, h357, hlam]
                                    · linarith only [h10, h357, hlam]
                                  · linarith only [h356, hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  rcases p353_3 (m.d 0 2) (by simp) with h361 | h361
                                  · rcases p353_3 (m.d 1 2) (by simp) with h362 | h362
                                    · linarith only [h0, h362, hlam]
                                    · linarith only [h11, h362, hlam]
                                  · linarith only [h361, hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h4, h6, h7, hlam, p188_1, p353_2]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h0, hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h0, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p353_1]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h0, h183, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p353_1]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  rcases p353_3 (m.d 0 2) (by simp) with h371 | h371
                                  · rcases p353_3 (m.d 1 2) (by simp) with h372 | h372
                                    · rcases p353_3 (m.d 2 3) (by simp) with h373 | h373
                                      · linarith only [h10, h373, hlam]
                                      · linarith only [h185, h373, hlam]
                                    · linarith only [h372, hlam, p353_0]
                                  · linarith only [h371, h6, hlam]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h4, hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h10, hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h183, hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p353_1]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h5, hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h11, hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p353_1]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h0, h11, h185, h187, hc01, hc45, hlam, hphi, ht0b, ht5b, p353_1]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h6, hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h12, hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h185, hlam, p353_1]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [h186, hlam, p353_0]
                                · have p353_0 := h353c.1
                                  have p353_1 := h353c.2.1
                                  have p353_2 := h353c.2.2.1
                                  have p353_3 := h353c.2.2.2
                                  linarith only [hlam, p353_0]
                              · linarith only [h0, h232, h4, h7, hc01, hlam, p188_1]
                          · linarith only [h229, h9, hlam]
                        · linarith only [h228, h8, hlam]
                      · linarith only [h227, h6, hlam]
                    · linarith only [h226, h3, hlam]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h3, hlam, p188_0]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h6, hlam, p188_1]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h8, hlam, p188_0]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [h9, hlam, p188_1]
                  · have p188_0 := h188c.1
                    have p188_1 := h188c.2.1
                    have p188_2 := h188c.2.2.1
                    have p188_3 := h188c.2.2.2
                    linarith only [hlam, p188_0]
                · linarith only [h0, h10, h13, h185, h187, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h13, h182, h183, h185, h186, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h405 | h405
              · rcases m.htr 3 4 5 (by decide) (by decide) with h406 | h406
                · rcases h0bigk with h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [hlam, p407_0]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h13, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h13, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h405, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h185, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h0, hlam, p407_0]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [hlam, p407_0]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h185, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h0, h405, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h0, h185, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h1, hlam, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h4, hlam, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [hlam, p407_0]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h405, h5, hc03, hc45, hlam, hphi, ht0b, ht5b, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h0, h185, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h2, hlam, p407_0]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h5, hlam, p407_0]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h7, hlam, p407_0]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [hlam, p407_0]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h185, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h3, hlam, p407_0]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h6, hlam, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h8, hlam, p407_0]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [h9, hlam, p407_1]
                  · have p407_0 := h407c.1
                    have p407_1 := h407c.2.1
                    have p407_2 := h407c.2.2.1
                    have p407_3 := h407c.2.2.2
                    linarith only [hlam, p407_0]
                · linarith only [h10, h11, h13, h2, h405, h406, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h434 | h434
                · rcases h0bigk with h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h13, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h13, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h183, h405, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h182, h183, h3, h405, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h0, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h183, h405, h434, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h0, h183, h405, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h0, h182, h183, h3, h405, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h1, hlam, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h4, hlam, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h183, h405, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h0, h182, h183, h3, h4, h405, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h2, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h5, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h7, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h182, h183, h3, h405, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h3, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h6, hlam, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h8, hlam, p435_0]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [h9, hlam, p435_1]
                  · have p435_0 := h435c.1
                    have p435_1 := h435c.2.1
                    have p435_2 := h435c.2.2.1
                    have p435_3 := h435c.2.2.2
                    linarith only [hlam, p435_0]
                · linarith only [h13, h182, h434, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h462 | h462
          · linarith only [h10, h13, h462, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h464 | h464
            · rcases m.htr 2 4 5 (by decide) (by decide) with h465 | h465
              · linarith only [h0, h11, h182, h465, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h462, h464, h465, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h468 | h468
              · linarith only [h0, h11, h13, h182, h468, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h470 | h470
                · rcases h0bigk with h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c | h471c
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [hlam, p471_0]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h10, h13, h182, h4, h470, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h10, h13, h182, h470, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h10, h13, h182, h470, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h10, h13, h182, h470, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h0, hlam, p471_0]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [hlam, p471_0]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h10, h13, h182, h470, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h0, h10, h13, h182, h470, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h0, h10, h13, h182, h470, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h1, hlam, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h4, hlam, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [hlam, p471_0]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h10, h13, h182, h470, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h0, h10, h13, h182, h4, h470, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h2, hlam, p471_0]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h5, hlam, p471_0]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h7, hlam, p471_0]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [hlam, p471_0]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h10, h13, h182, h470, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h3, hlam, p471_0]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h6, hlam, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h8, hlam, p471_0]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [h9, hlam, p471_1]
                  · have p471_0 := h471c.1
                    have p471_1 := h471c.2.1
                    have p471_2 := h471c.2.2.1
                    have p471_3 := h471c.2.2.2
                    linarith only [hlam, p471_0]
                · rcases h0bigk with h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [hlam, p497_0]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h0, h12, hc01, hc25, hlam, hphi, ht0b, ht5b, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h10, h13, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h10, h13, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h10, h13, h470, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h0, hlam, p497_0]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [hlam, p497_0]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h10, h13, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h0, h10, h13, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h0, h10, h13, h470, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h1, hlam, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h4, hlam, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [hlam, p497_0]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h10, h13, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h0, h10, h13, h4, h470, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h2, hlam, p497_0]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h5, hlam, p497_0]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h7, hlam, p497_0]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [hlam, p497_0]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h10, h13, h470, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h3, hlam, p497_0]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h6, hlam, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h8, hlam, p497_0]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [h9, hlam, p497_1]
                  · have p497_0 := h497c.1
                    have p497_1 := h497c.2.1
                    have p497_2 := h497c.2.2.1
                    have p497_3 := h497c.2.2.2
                    linarith only [hlam, p497_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h523 | h523
      · rcases m.htr 1 4 5 (by decide) (by decide) with h524 | h524
        · linarith only [h11, h12, h524, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h526 | h526
          · linarith only [h0, h10, h12, h526, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h12, h523, h526, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h529 | h529
        · linarith only [h11, h12, h529, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h531 | h531
          · linarith only [h0, h10, h12, h523, h531, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h533 | h533
            · linarith only [h0, h10, h12, h533, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h535 | h535
              · linarith only [h0, h11, h12, h4, h533, h535, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h537 | h537
                · linarith only [h11, h12, h531, h535, h537, hc23, hc34, hlam, hphi]
                · rcases h0bigk with h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h11, h12, h4, h531, h533, h537, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h11, h12, h531, h533, h537, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h11, h12, h531, h533, h537, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h11, h12, h531, h533, h537, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h0, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h11, h12, h531, h533, h537, h7, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h0, h11, h12, h531, h533, h537, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h0, h11, h12, h531, h533, h537, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h1, hlam, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h4, hlam, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h11, h12, h531, h533, h537, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h0, h11, h12, h4, h531, h533, h537, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h2, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h5, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h7, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h11, h12, h531, h533, h537, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h3, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h6, hlam, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h8, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h9, hlam, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [hlam, p539_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h565 | h565
    · rcases m.htr 1 3 4 (by decide) (by decide) with h566 | h566
      · linarith only [h10, h11, h566, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h568 | h568
        · rcases m.htr 2 3 4 (by decide) (by decide) with h569 | h569
          · linarith only [h0, h10, h11, h5, h566, h569, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h571 | h571
            · linarith only [h0, h10, h11, h4, h569, h571, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h573 | h573
              · rcases m.htr 3 4 5 (by decide) (by decide) with h574 | h574
                · rcases h0bigk with h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [hlam, p575_0]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h11, h4, h569, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h11, h565, h569, h571, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h11, h2, h565, h571, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h571, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h0, hlam, p575_0]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [hlam, p575_0]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h11, h565, h569, h571, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h0, h11, h565, h569, h571, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h0, h571, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h1, hlam, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h4, hlam, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [hlam, p575_0]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h11, h565, h569, h571, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h0, h4, h571, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h2, hlam, p575_0]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h5, hlam, p575_0]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h7, hlam, p575_0]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [hlam, p575_0]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h571, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h3, hlam, p575_0]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h6, hlam, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h8, hlam, p575_0]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [h9, hlam, p575_1]
                  · have p575_0 := h575c.1
                    have p575_1 := h575c.2.1
                    have p575_2 := h575c.2.2.1
                    have p575_3 := h575c.2.2.2
                    linarith only [hlam, p575_0]
                · linarith only [h11, h565, h569, h573, h574, hlam]
              · linarith only [h11, h565, h571, h573, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h11, h565, h568, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h604 | h604
      · linarith only [h10, h11, h604, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h606 | h606
        · rcases m.htr 2 3 4 (by decide) (by decide) with h607 | h607
          · linarith only [h0, h10, h11, h5, h604, h607, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h609 | h609
            · linarith only [h0, h10, h11, h4, h607, h609, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h611 | h611
              · rcases m.htr 3 4 5 (by decide) (by decide) with h612 | h612
                · rcases h0bigk with h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [hlam, p613_0]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h4, h565, h607, h611, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h10, h565, h607, h611, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h10, h2, h565, h606, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h10, h3, h565, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h0, hlam, p613_0]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [hlam, p613_0]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h10, h565, h607, h611, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h0, h10, h2, h565, h606, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h0, h10, h3, h565, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h1, hlam, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h4, hlam, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [hlam, p613_0]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h10, h5, h565, h611, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h0, h10, h4, h565, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h2, hlam, p613_0]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h5, hlam, p613_0]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h7, hlam, p613_0]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [hlam, p613_0]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h10, h565, h609, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h3, hlam, p613_0]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h6, hlam, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h8, hlam, p613_0]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [h9, hlam, p613_1]
                  · have p613_0 := h613c.1
                    have p613_1 := h613c.2.1
                    have p613_2 := h613c.2.2.1
                    have p613_3 := h613c.2.2.2
                    linarith only [hlam, p613_0]
                · linarith only [h10, h565, h606, h607, h611, h612, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h11, h606, h611, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h641 | h641
          · linarith only [h0, h10, h11, h5, h641, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h643 | h643
            · linarith only [h0, h10, h11, h4, h606, h643, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h645 | h645
              · linarith only [h0, h10, h11, h4, h606, h641, h645, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h10, h11, h645, hc23, hc45, hlam, hphi, ht34]

end R2N4
