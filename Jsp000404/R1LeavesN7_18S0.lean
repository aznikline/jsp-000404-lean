import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
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
                    linarith only [h17, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p23_1]
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
                    linarith only [h15, h17, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
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
            · linarith only [h1, h14, h15, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h50 | h50
            · linarith only [h1, h13, h15, h50, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
              · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                · rcases h0bigk with h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h0, h10, h13, h50, h53, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h1, h13, h50, h53, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h5, h52, hc01, hc45, hlam, hphi, ht0b, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h50, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h0, hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h1, h13, h50, h53, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h0, h50, h53, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h0, h50, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h1, hlam, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h4, hlam, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h50, h53, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h0, h4, h50, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h2, hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h5, hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h7, hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h50, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h3, hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h6, hlam, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h8, hlam, p54_0]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [h9, hlam, p54_1]
                  · have p54_0 := h54c.1
                    have p54_1 := h54c.2.1
                    have p54_2 := h54c.2.2.1
                    have p54_3 := h54c.2.2.2
                    linarith only [hlam, p54_0]
                · linarith only [h0, h11, h52, h53, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
                · linarith only [h0, h10, h13, h15, h52, h81, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases h0bigk with h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [hlam, p83_0]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h4, h7, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h7, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h14, h15, h3, h81, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h0, hlam, p83_0]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [hlam, p83_0]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h0, h15, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h0, h13, h15, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h0, h14, h15, h3, h81, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h1, hlam, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h4, hlam, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [hlam, p83_0]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h13, h15, h2, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h0, h14, h15, h3, h4, h81, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h2, hlam, p83_0]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h5, hlam, p83_0]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h7, hlam, p83_0]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [hlam, p83_0]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h14, h15, h3, h81, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h3, hlam, p83_0]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h6, hlam, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h8, hlam, p83_0]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [h9, hlam, p83_1]
                  · have p83_0 := h83c.1
                    have p83_1 := h83c.2.1
                    have p83_2 := h83c.2.2.1
                    have p83_3 := h83c.2.2.2
                    linarith only [hlam, p83_0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
          · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
            · linarith only [h10, h110, h14, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h112 | h112
              · linarith only [h109, h110, h112, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h114 | h114
                · linarith only [h112, h114, h13, h14, h8, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h0bigk with h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [hlam, p116_0]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h114, h14, h4, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h114, h14, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h114, h14, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h109, h110, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h0, hlam, p116_0]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [hlam, p116_0]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h114, h14, h7, h9, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h0, h114, h14, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h0, h109, h110, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h1, hlam, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h4, hlam, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [hlam, p116_0]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h114, h14, h9, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h0, h109, h110, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h2, hlam, p116_0]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h5, hlam, p116_0]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h7, hlam, p116_0]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [hlam, p116_0]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h109, h110, h6, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h3, hlam, p116_0]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h6, hlam, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h8, hlam, p116_0]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [h9, hlam, p116_1]
                  · have p116_0 := h116c.1
                    have p116_1 := h116c.2.1
                    have p116_2 := h116c.2.2.1
                    have p116_3 := h116c.2.2.2
                    linarith only [hlam, p116_0]
          · linarith only [h109, h13, h14, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h143 | h143
        · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
          · linarith only [h0, h13, h143, h144, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
            · rcases m.htr 2 4 5 (by decide) (by decide) with h147 | h147
              · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                · rcases h0bigk with h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [hlam, p149_0]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h1, h10, h146, h148, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h1, h10, h146, h148, hc01, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h10, h13, h146, h148, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    rcases p149_3 (m.d 0 1) (by simp) with h154 | h154
                    · rcases p149_3 (m.d 0 2) (by simp) with h155 | h155
                      · linarith only [h0, h155, hlam]
                      · linarith only [h155, h6, hlam]
                    · linarith only [h154, h3, hlam]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h0, hlam, p149_0]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [hlam, p149_0]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h10, h13, h146, h148, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h0, h10, h13, h146, h148, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    rcases p149_3 (m.d 0 1) (by simp) with h163 | h163
                    · rcases p149_3 (m.d 0 2) (by simp) with h164 | h164
                      · rcases p149_3 (m.d 0 3) (by simp) with h165 | h165
                        · linarith only [h165, h4, hlam]
                        · linarith only [h165, h8, hlam]
                      · linarith only [h164, h6, hlam]
                    · linarith only [h163, h3, hlam]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h1, hlam, p149_1]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h4, hlam, p149_1]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [hlam, p149_0]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h10, h13, h146, h148, h7, hc03, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    rcases p149_3 (m.d 0 1) (by simp) with h174 | h174
                    · rcases p149_3 (m.d 0 2) (by simp) with h175 | h175
                      · rcases p149_3 (m.d 0 3) (by simp) with h176 | h176
                        · rcases p149_3 (m.d 0 4) (by simp) with h177 | h177
                          · linarith only [h177, h7, hlam]
                          · linarith only [h177, h9, hlam]
                        · linarith only [h176, h8, hlam]
                      · linarith only [h175, h6, hlam]
                    · linarith only [h174, h3, hlam]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h2, hlam, p149_0]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h5, hlam, p149_0]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h7, hlam, p149_0]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [hlam, p149_0]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    rcases p149_3 (m.d 0 1) (by simp) with h187 | h187
                    · rcases p149_3 (m.d 0 2) (by simp) with h188 | h188
                      · rcases p149_3 (m.d 0 3) (by simp) with h189 | h189
                        · rcases p149_3 (m.d 0 4) (by simp) with h190 | h190
                          · rcases p149_3 (m.d 0 5) (by simp) with h191 | h191
                            · linarith only [h191, h9, hlam]
                            · rcases h2bigk with h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h0, h10, h146, h148, hc01, hc45, hlam, hphi, ht0b, ht5b, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                rcases p193_3 (m.d 0 2) (by simp) with h196 | h196
                                · rcases p193_3 (m.d 1 2) (by simp) with h197 | h197
                                  · linarith only [h0, h197, hlam]
                                  · linarith only [h10, h197, hlam]
                                · linarith only [h196, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                rcases p193_3 (m.d 0 2) (by simp) with h201 | h201
                                · rcases p193_3 (m.d 1 2) (by simp) with h202 | h202
                                  · linarith only [h0, h202, hlam]
                                  · linarith only [h11, h202, hlam]
                                · linarith only [h201, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h4, h6, h7, hlam, p149_1, p193_2]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h0, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h0, h146, h148, hc01, hc45, hlam, hphi, ht0b, ht5b, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h0, h144, h146, h148, hc01, hc45, hlam, hphi, ht0b, ht5b, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                rcases p193_3 (m.d 0 2) (by simp) with h211 | h211
                                · rcases p193_3 (m.d 1 2) (by simp) with h212 | h212
                                  · rcases p193_3 (m.d 2 3) (by simp) with h213 | h213
                                    · linarith only [h10, h213, hlam]
                                    · linarith only [h146, h213, hlam]
                                  · linarith only [h212, hlam, p193_0]
                                · linarith only [h211, h6, hlam]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h4, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h10, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h144, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h0, h10, h13, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h5, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h11, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h0, h11, h146, h148, hc01, hc45, hlam, hphi, ht0b, ht5b, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h6, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h12, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h146, hlam, p193_1]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [h147, hlam, p193_0]
                              · have p193_0 := h193c.1
                                have p193_1 := h193c.2.1
                                have p193_2 := h193c.2.2.1
                                have p193_3 := h193c.2.2.2
                                linarith only [hlam, p193_0]
                          · linarith only [h190, h9, hlam]
                        · linarith only [h189, h8, hlam]
                      · linarith only [h188, h6, hlam]
                    · linarith only [h187, h3, hlam]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h3, hlam, p149_0]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h6, hlam, p149_1]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h8, hlam, p149_0]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [h9, hlam, p149_1]
                  · have p149_0 := h149c.1
                    have p149_1 := h149c.2.1
                    have p149_2 := h149c.2.2.1
                    have p149_3 := h149c.2.2.2
                    linarith only [hlam, p149_0]
                · linarith only [h0, h10, h13, h146, h148, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h144, h146, h147, hlam]
            · linarith only [h0, h13, h143, h146, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
          · linarith only [h0, h10, h13, h245, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h247 | h247
            · linarith only [h10, h143, h247, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h249 | h249
              · rcases m.htr 3 4 5 (by decide) (by decide) with h250 | h250
                · rcases h0bigk with h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [hlam, p251_0]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h11, h2, h249, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h11, h2, h249, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h11, h2, h249, hc01, hc45, hlam, hphi, ht0b, ht5b, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h10, h143, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h0, hlam, p251_0]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [hlam, p251_0]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h11, h2, h249, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h0, h11, h2, h249, hc01, hc45, hlam, hphi, ht0b, ht5b, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h0, h10, h143, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h1, hlam, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h4, hlam, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [hlam, p251_0]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h11, h2, h249, hc03, hc45, hlam, hphi, ht0b, ht5b, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h0, h10, h143, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h2, hlam, p251_0]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h5, hlam, p251_0]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h7, hlam, p251_0]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [hlam, p251_0]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h10, h143, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h3, hlam, p251_0]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h6, hlam, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h8, hlam, p251_0]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [h9, hlam, p251_1]
                  · have p251_0 := h251c.1
                    have p251_1 := h251c.2.1
                    have p251_2 := h251c.2.2.1
                    have p251_3 := h251c.2.2.2
                    linarith only [hlam, p251_0]
                · linarith only [h0, h11, h249, h250, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h278 | h278
                · rcases h0bigk with h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h249, h278, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h249, h278, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h249, h278, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h249, h278, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h0, hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h249, h278, h7, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h0, h249, h278, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h0, h249, h278, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h1, hlam, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h4, hlam, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h249, h278, h7, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h0, h249, h278, h4, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h2, hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h5, hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h7, hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h249, h278, h8, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h3, hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h6, hlam, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h8, hlam, p279_0]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [h9, hlam, p279_1]
                  · have p279_0 := h279c.1
                    have p279_1 := h279c.2.1
                    have p279_2 := h279c.2.2.1
                    have p279_3 := h279c.2.2.2
                    linarith only [hlam, p279_0]
                · rcases h0bigk with h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [hlam, p305_0]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h4, h7, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h7, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h10, h13, h278, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h0, hlam, p305_0]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [hlam, p305_0]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h10, h13, h278, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h0, h10, h13, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h0, h10, h13, h278, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h1, hlam, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h4, hlam, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [hlam, p305_0]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h10, h13, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h0, h10, h13, h278, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h2, hlam, p305_0]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h5, hlam, p305_0]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h7, hlam, p305_0]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [hlam, p305_0]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h10, h13, h278, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h3, hlam, p305_0]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h6, hlam, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h8, hlam, p305_0]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [h9, hlam, p305_1]
                  · have p305_0 := h305c.1
                    have p305_1 := h305c.2.1
                    have p305_2 := h305c.2.2.1
                    have p305_3 := h305c.2.2.2
                    linarith only [hlam, p305_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h331 | h331
      · rcases m.htr 1 3 5 (by decide) (by decide) with h332 | h332
        · linarith only [h10, h12, h332, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h334 | h334
          · linarith only [h0, h10, h12, h334, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h12, h331, h334, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h337 | h337
        · linarith only [h11, h12, h331, h337, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h339 | h339
          · linarith only [h0, h10, h12, h331, h339, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h341 | h341
            · linarith only [h10, h12, h337, h341, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h343 | h343
              · linarith only [h0, h11, h12, h341, h343, h4, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h345 | h345
                · linarith only [h0, h11, h12, h343, h345, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h0bigk with h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [hlam, p347_0]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h345, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h345, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h345, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h11, h12, h3, h339, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h0, hlam, p347_0]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [hlam, p347_0]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h345, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h0, h345, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h0, h11, h12, h3, h339, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h1, hlam, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h4, hlam, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [hlam, p347_0]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h345, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h0, h11, h12, h339, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h2, hlam, p347_0]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h5, hlam, p347_0]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h7, hlam, p347_0]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [hlam, p347_0]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h11, h12, h339, h6, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h3, hlam, p347_0]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h6, hlam, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h8, hlam, p347_0]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [h9, hlam, p347_1]
                  · have p347_0 := h347c.1
                    have p347_1 := h347c.2.1
                    have p347_2 := h347c.2.2.1
                    have p347_3 := h347c.2.2.2
                    linarith only [hlam, p347_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h373 | h373
    · rcases m.htr 1 3 4 (by decide) (by decide) with h374 | h374
      · linarith only [h10, h11, h374, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h376 | h376
        · rcases m.htr 2 3 4 (by decide) (by decide) with h377 | h377
          · linarith only [h0, h374, h376, h377, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h379 | h379
            · linarith only [h0, h10, h11, h377, h379, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h11, h376, h377, h379, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h382 | h382
          · linarith only [h0, h10, h11, h382, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h384 | h384
            · linarith only [h0, h10, h11, h376, h382, h384, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h386 | h386
              · rcases m.htr 3 4 5 (by decide) (by decide) with h387 | h387
                · rcases h0bigk with h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [hlam, p388_0]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h11, h382, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h11, h382, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h11, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h10, h376, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h0, hlam, p388_0]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [hlam, p388_0]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h11, h382, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h0, h11, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h0, h10, h376, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h1, hlam, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h4, hlam, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [hlam, p388_0]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h11, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h0, h10, h376, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h2, hlam, p388_0]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h5, hlam, p388_0]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h7, hlam, p388_0]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [hlam, p388_0]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h10, h376, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h3, hlam, p388_0]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h6, hlam, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h8, hlam, p388_0]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [h9, hlam, p388_1]
                  · have p388_0 := h388c.1
                    have p388_1 := h388c.2.1
                    have p388_2 := h388c.2.2.1
                    have p388_3 := h388c.2.2.2
                    linarith only [hlam, p388_0]
                · linarith only [h11, h373, h382, h386, h387, hlam]
              · linarith only [h11, h373, h384, h386, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h416 | h416
      · linarith only [h10, h11, h416, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h418 | h418
        · linarith only [h10, h373, h418, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h420 | h420
          · linarith only [h0, h10, h11, h416, h420, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h422 | h422
            · linarith only [h10, h373, h418, h422, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h424 | h424
              · rcases m.htr 3 4 5 (by decide) (by decide) with h425 | h425
                · rcases h0bigk with h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [hlam, p426_0]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h373, h4, h420, h424, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h10, h373, h420, h424, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h10, h11, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h10, h3, h373, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h0, hlam, p426_0]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [hlam, p426_0]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h10, h373, h420, h424, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h0, h10, h11, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h0, h10, h3, h373, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h1, hlam, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h4, hlam, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [hlam, p426_0]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h10, h373, h424, h5, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h0, h10, h373, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h2, hlam, p426_0]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h5, hlam, p426_0]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h7, hlam, p426_0]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [hlam, p426_0]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h10, h373, h422, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h3, hlam, p426_0]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h6, hlam, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h8, hlam, p426_0]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [h9, hlam, p426_1]
                  · have p426_0 := h426c.1
                    have p426_1 := h426c.2.1
                    have p426_2 := h426c.2.2.1
                    have p426_3 := h426c.2.2.2
                    linarith only [hlam, p426_0]
                · linarith only [h420, h424, h425, hlam]
              · linarith only [h0, h10, h11, h4, h424, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

end R2N4
