import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
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
      · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
        · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
          · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
            · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
              · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h10, h16, h19, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h10, h16, h18, h19, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h10, h13, h18, h22, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h17, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h16, h18, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h16, h18, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
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
                      linarith only [h16, h18, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, h16, h18, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, h16, h18, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h1, hlam, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h4, hlam, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h16, h18, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, h16, h18, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h2, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h5, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h7, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h0, h16, h18, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h3, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h6, hlam, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h8, hlam, p24_0]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h9, hlam, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [hlam, p24_0]
              · linarith only [h0, h10, h14, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h51 | h51
              · linarith only [h0, h10, h13, h16, h51, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                  · rcases h0bigk with h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h0, h10, h13, h51, h54, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h1, h13, h51, h54, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h51, h54, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h51, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h0, hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h1, h13, h51, h54, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h0, h51, h54, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h0, h51, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h1, hlam, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h4, hlam, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h51, h54, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h0, h4, h51, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h2, hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h5, hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h7, hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h51, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h3, hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h6, hlam, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h8, hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h9, hlam, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [hlam, p55_0]
                  · linarith only [h0, h10, h13, h15, h16, h54, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h0, h10, h13, h53, h82, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h10, h13, h15, h16, h82, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
            · rcases m.htr 2 3 5 (by decide) (by decide) with h86 | h86
              · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                · linarith only [h0, h11, h15, h87, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                  · linarith only [h11, h15, h85, h89, hlam]
                  · rcases h0bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h4, h86, h89, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h4, h86, h89, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h11, h15, h85, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h11, h15, h85, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h0, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h11, h15, h7, h85, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h0, h11, h15, h85, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h0, h11, h15, h85, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h1, hlam, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h4, hlam, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h11, h15, h85, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h0, h11, h15, h4, h85, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h2, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h5, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h7, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h0, h11, h15, h4, h7, h85, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h3, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h6, hlam, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h8, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h9, hlam, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hlam, p91_0]
              · linarith only [h0, h10, h14, h85, h86, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
              · linarith only [h0, h118, h13, h15, h4, h7, h85, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h120 | h120
                · linarith only [h120, h13, h15, h85, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                  · linarith only [h122, h13, h15, hlam]
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
                      linarith only [h15, h4, h7, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p124_1]
                    · have p124_0 := h124c.1
                      have p124_1 := h124c.2.1
                      have p124_2 := h124c.2.2.1
                      have p124_3 := h124c.2.2.2
                      linarith only [h13, h15, h7, h85, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                    · have p124_0 := h124c.1
                      have p124_1 := h124c.2.1
                      have p124_2 := h124c.2.2.1
                      have p124_3 := h124c.2.2.2
                      linarith only [h13, h15, h85, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                    · have p124_0 := h124c.1
                      have p124_1 := h124c.2.1
                      have p124_2 := h124c.2.2.1
                      have p124_3 := h124c.2.2.2
                      linarith only [h13, h15, h3, h85, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
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
                      linarith only [h13, h15, h7, h85, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                    · have p124_0 := h124c.1
                      have p124_1 := h124c.2.1
                      have p124_2 := h124c.2.2.1
                      have p124_3 := h124c.2.2.2
                      linarith only [h0, h13, h15, h85, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                    · have p124_0 := h124c.1
                      have p124_1 := h124c.2.1
                      have p124_2 := h124c.2.2.1
                      have p124_3 := h124c.2.2.2
                      linarith only [h0, h13, h15, h3, h85, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
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
                      linarith only [h13, h15, h85, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
                    · have p124_0 := h124c.1
                      have p124_1 := h124c.2.1
                      have p124_2 := h124c.2.2.1
                      have p124_3 := h124c.2.2.2
                      linarith only [h0, h13, h15, h3, h4, h85, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
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
                      linarith only [h13, h15, h3, h85, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1]
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
        · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
          · linarith only [h13, h14, h150, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
            · rcases m.htr 2 3 5 (by decide) (by decide) with h153 | h153
              · linarith only [h0, h10, h14, h153, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h155 | h155
                · linarith only [h0, h10, h11, h14, h150, h152, h155, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h157 | h157
                  · linarith only [h10, h14, h150, h152, h157, h8, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [hlam, p159_0]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h14, h157, h4, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h10, h14, h157, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h10, h14, h157, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h10, h14, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h0, hlam, p159_0]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [hlam, p159_0]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h10, h14, h157, h7, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h0, h10, h14, h157, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h0, h10, h14, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h1, hlam, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h4, hlam, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [hlam, p159_0]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h10, h14, h157, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h0, h10, h14, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h2, hlam, p159_0]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h5, hlam, p159_0]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h7, hlam, p159_0]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [hlam, p159_0]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h10, h14, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h3, hlam, p159_0]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h6, hlam, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h8, hlam, p159_0]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [h9, hlam, p159_1]
                    · have p159_0 := h159c.1
                      have p159_1 := h159c.2.1
                      have p159_2 := h159c.2.2.1
                      have p159_3 := h159c.2.2.2
                      linarith only [hlam, p159_0]
            · linarith only [h13, h14, h152, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h186 | h186
        · rcases m.htr 1 4 5 (by decide) (by decide) with h187 | h187
          · rcases m.htr 2 3 4 (by decide) (by decide) with h188 | h188
            · linarith only [h0, h10, h13, h188, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h190 | h190
              · rcases m.htr 2 4 5 (by decide) (by decide) with h191 | h191
                · rcases m.htr 3 4 5 (by decide) (by decide) with h192 | h192
                  · rcases h0bigk with h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [hlam, p193_0]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h1, h10, h190, h192, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p193_1]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h1, h10, h190, h192, hc01, hc45, hlam, hphi, ht0b, ht5b, p193_1]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h10, h13, h190, h192, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p193_1]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      rcases p193_3 (m.d 0 1) (by simp) with h198 | h198
                      · rcases p193_3 (m.d 0 2) (by simp) with h199 | h199
                        · linarith only [h0, h199, hlam]
                        · linarith only [h199, h6, hlam]
                      · linarith only [h198, h3, hlam]
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
                      linarith only [h10, h13, h190, h192, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p193_1]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h0, h10, h13, h190, h192, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p193_1]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      rcases p193_3 (m.d 0 1) (by simp) with h207 | h207
                      · rcases p193_3 (m.d 0 2) (by simp) with h208 | h208
                        · rcases p193_3 (m.d 0 3) (by simp) with h209 | h209
                          · linarith only [h209, h4, hlam]
                          · linarith only [h209, h8, hlam]
                        · linarith only [h208, h6, hlam]
                      · linarith only [h207, h3, hlam]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h1, hlam, p193_1]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h4, hlam, p193_1]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [hlam, p193_0]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h10, h13, h190, h192, h7, hc03, hc45, hlam, hphi, ht0b, ht5b, p193_1]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      rcases p193_3 (m.d 0 1) (by simp) with h218 | h218
                      · rcases p193_3 (m.d 0 2) (by simp) with h219 | h219
                        · rcases p193_3 (m.d 0 3) (by simp) with h220 | h220
                          · rcases p193_3 (m.d 0 4) (by simp) with h221 | h221
                            · linarith only [h221, h7, hlam]
                            · linarith only [h221, h9, hlam]
                          · linarith only [h220, h8, hlam]
                        · linarith only [h219, h6, hlam]
                      · linarith only [h218, h3, hlam]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h2, hlam, p193_0]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h5, hlam, p193_0]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h7, hlam, p193_0]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [hlam, p193_0]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      rcases p193_3 (m.d 0 1) (by simp) with h231 | h231
                      · rcases p193_3 (m.d 0 2) (by simp) with h232 | h232
                        · rcases p193_3 (m.d 0 3) (by simp) with h233 | h233
                          · rcases p193_3 (m.d 0 4) (by simp) with h234 | h234
                            · rcases p193_3 (m.d 0 5) (by simp) with h235 | h235
                              · linarith only [h235, h9, hlam]
                              · rcases h1bigk with h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [hlam, p237_0]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h10, h190, h192, hc01, hc45, hlam, hphi, ht0b, ht5b, p237_1]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  rcases p237_3 (m.d 0 1) (by simp) with h240 | h240
                                  · rcases p237_3 (m.d 1 2) (by simp) with h241 | h241
                                    · linarith only [h0, h241, hlam]
                                    · linarith only [h10, h241, hlam]
                                  · linarith only [h240, hlam, p237_0]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  rcases p237_3 (m.d 0 1) (by simp) with h245 | h245
                                  · rcases p237_3 (m.d 1 2) (by simp) with h246 | h246
                                    · linarith only [h0, h246, hlam]
                                    · linarith only [h11, h246, hlam]
                                  · linarith only [h245, hlam, p237_0]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h0, h3, h4, h7, hlam, p193_1, p237_2]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h0, hlam, p237_0]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [hlam, p237_0]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h0, h10, h190, h192, hc01, hc45, hlam, hphi, ht0b, ht5b, p237_1]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h0, h10, h13, h190, h192, hc01, hc45, hlam, hphi, ht0b, ht5b, p237_1]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  rcases p237_3 (m.d 0 1) (by simp) with h255 | h255
                                  · rcases p237_3 (m.d 1 2) (by simp) with h256 | h256
                                    · rcases p237_3 (m.d 1 3) (by simp) with h257 | h257
                                      · linarith only [h10, h257, hlam]
                                      · linarith only [h186, h257, hlam]
                                    · linarith only [h12, h256, hlam]
                                  · linarith only [h255, h3, hlam]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h1, hlam, p237_0]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h10, hlam, p237_1]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [hlam, p237_0]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h13, hlam, p237_1]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h0, h12, h13, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p237_1]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h2, hlam, p237_0]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h11, hlam, p237_1]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h10, h190, h192, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p237_1]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [hlam, p237_0]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  rcases p237_3 (m.d 0 1) (by simp) with h271 | h271
                                  · rcases p237_3 (m.d 1 2) (by simp) with h272 | h272
                                    · rcases p237_3 (m.d 1 3) (by simp) with h273 | h273
                                      · linarith only [h13, h273, hlam]
                                      · linarith only [h186, h273, hlam]
                                    · linarith only [h12, h272, hlam]
                                  · linarith only [h271, h3, hlam]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h3, hlam, p237_0]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h12, hlam, p237_1]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h186, hlam, p237_0]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [h187, hlam, p237_0]
                                · have p237_0 := h237c.1
                                  have p237_1 := h237c.2.1
                                  have p237_2 := h237c.2.2.1
                                  have p237_3 := h237c.2.2.2
                                  linarith only [hlam, p237_0]
                            · linarith only [h234, h9, hlam]
                          · linarith only [h233, h8, hlam]
                        · linarith only [h232, h6, hlam]
                      · linarith only [h231, h3, hlam]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h3, hlam, p193_0]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h6, hlam, p193_1]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h8, hlam, p193_0]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [h9, hlam, p193_1]
                    · have p193_0 := h193c.1
                      have p193_1 := h193c.2.1
                      have p193_2 := h193c.2.2.1
                      have p193_3 := h193c.2.2.2
                      linarith only [hlam, p193_0]
                  · linarith only [h0, h10, h13, h190, h192, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h13, h186, h187, h188, h190, h191, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h13, h186, h190, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h13, h186, h187, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h296 | h296
          · rcases m.htr 2 3 4 (by decide) (by decide) with h297 | h297
            · linarith only [h10, h13, h297, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h299 | h299
              · linarith only [h10, h186, h299, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h301 | h301
                · rcases m.htr 3 4 5 (by decide) (by decide) with h302 | h302
                  · rcases h0bigk with h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c | h303c
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [hlam, p303_0]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h0, h11, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h301, h5, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h301, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h10, h186, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h0, hlam, p303_0]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [hlam, p303_0]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h301, h5, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h0, h301, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h0, h10, h186, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h1, hlam, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h4, hlam, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [hlam, p303_0]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h301, h5, hc03, hc45, hlam, hphi, ht0b, ht5b, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h0, h10, h186, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h2, hlam, p303_0]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h5, hlam, p303_0]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h7, hlam, p303_0]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [hlam, p303_0]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h10, h186, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h3, hlam, p303_0]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h6, hlam, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h8, hlam, p303_0]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [h9, hlam, p303_1]
                    · have p303_0 := h303c.1
                      have p303_1 := h303c.2.1
                      have p303_2 := h303c.2.2.1
                      have p303_3 := h303c.2.2.2
                      linarith only [hlam, p303_0]
                  · linarith only [h0, h11, h13, h301, h302, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h330 | h330
                  · rcases h0bigk with h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [hlam, p331_0]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h2, h296, h297, h301, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h2, h296, h297, h301, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h2, h296, h297, h301, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h186, h296, h297, h301, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h0, hlam, p331_0]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [hlam, p331_0]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h2, h296, h297, h301, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h0, h2, h296, h297, h301, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h0, h186, h296, h297, h301, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h1, hlam, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h4, hlam, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [hlam, p331_0]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h2, h296, h297, h301, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h0, h186, h296, h297, h301, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h2, hlam, p331_0]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h5, hlam, p331_0]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h7, hlam, p331_0]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [hlam, p331_0]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h186, h296, h297, h301, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h3, hlam, p331_0]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h6, hlam, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h8, hlam, p331_0]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [h9, hlam, p331_1]
                    · have p331_0 := h331c.1
                      have p331_1 := h331c.2.1
                      have p331_2 := h331c.2.2.1
                      have p331_3 := h331c.2.2.2
                      linarith only [hlam, p331_0]
                  · linarith only [h13, h296, h330, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h358 | h358
            · linarith only [h10, h13, h358, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h360 | h360
              · linarith only [h10, h186, h360, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h362 | h362
                · linarith only [h11, h296, h362, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h364 | h364
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
                      linarith only [h296, h364, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h11, h296, h364, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h11, h296, h364, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h11, h296, h364, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p365_1]
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
                      linarith only [h11, h296, h364, h7, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h0, h11, h296, h364, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h0, h11, h296, h364, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p365_1]
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
                      linarith only [h11, h296, h364, h7, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p365_1]
                    · have p365_0 := h365c.1
                      have p365_1 := h365c.2.1
                      have p365_2 := h365c.2.2.1
                      have p365_3 := h365c.2.2.2
                      linarith only [h0, h11, h296, h364, h4, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p365_1]
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
                      linarith only [h11, h296, h364, h8, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p365_1]
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
                  · rcases h0bigk with h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [hlam, p391_0]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h10, h13, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h10, h13, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h10, h13, h364, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h0, hlam, p391_0]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [hlam, p391_0]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h10, h13, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h0, h10, h13, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h0, h10, h13, h364, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h1, hlam, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h4, hlam, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [hlam, p391_0]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h0, h10, h13, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h0, h10, h13, h364, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h2, hlam, p391_0]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h5, hlam, p391_0]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h7, hlam, p391_0]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [hlam, p391_0]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h10, h13, h364, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h3, hlam, p391_0]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h6, hlam, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h8, hlam, p391_0]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [h9, hlam, p391_1]
                    · have p391_0 := h391c.1
                      have p391_1 := h391c.2.1
                      have p391_2 := h391c.2.2.1
                      have p391_3 := h391c.2.2.2
                      linarith only [hlam, p391_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h417 | h417
      · rcases m.htr 1 3 5 (by decide) (by decide) with h418 | h418
        · linarith only [h10, h12, h418, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h420 | h420
          · linarith only [h11, h12, h420, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h422 | h422
            · linarith only [h0, h10, h12, h422, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h12, h417, h422, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h425 | h425
        · linarith only [h11, h12, h417, h425, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h427 | h427
          · linarith only [h11, h12, h427, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h429 | h429
            · linarith only [h0, h10, h12, h417, h429, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h431 | h431
              · linarith only [h10, h12, h425, h431, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h433 | h433
                · linarith only [h0, h11, h12, h4, h431, h433, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h435 | h435
                  · linarith only [h0, h11, h12, h4, h429, h433, h435, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases h0bigk with h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [hlam, p437_0]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h4, h417, h435, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h417, h435, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h417, h435, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h11, h12, h3, h429, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h0, hlam, p437_0]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [hlam, p437_0]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h417, h435, h7, h9, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h0, h417, h435, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h0, h11, h12, h3, h429, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h1, hlam, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h4, hlam, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [hlam, p437_0]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h417, h435, h9, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h0, h11, h12, h4, h429, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h2, hlam, p437_0]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h5, hlam, p437_0]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h7, hlam, p437_0]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [hlam, p437_0]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h11, h12, h429, h6, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h3, hlam, p437_0]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h6, hlam, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h8, hlam, p437_0]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [h9, hlam, p437_1]
                    · have p437_0 := h437c.1
                      have p437_1 := h437c.2.1
                      have p437_2 := h437c.2.2.1
                      have p437_3 := h437c.2.2.2
                      linarith only [hlam, p437_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h463 | h463
    · rcases m.htr 1 3 4 (by decide) (by decide) with h464 | h464
      · linarith only [h10, h11, h464, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h466 | h466
        · rcases m.htr 1 4 5 (by decide) (by decide) with h467 | h467
          · rcases m.htr 2 3 4 (by decide) (by decide) with h468 | h468
            · linarith only [h0, h4, h464, h466, h468, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h470 | h470
              · linarith only [h0, h10, h11, h4, h468, h470, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h10, h11, h4, h466, h468, h470, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h11, h463, h467, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h474 | h474
          · rcases m.htr 2 3 4 (by decide) (by decide) with h475 | h475
            · linarith only [h0, h10, h464, h474, h475, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h477 | h477
              · linarith only [h10, h466, h477, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h479 | h479
                · rcases m.htr 3 4 5 (by decide) (by decide) with h480 | h480
                  · rcases h0bigk with h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [hlam, p481_0]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h0, h463, h477, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h11, h2, h463, h477, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h11, h2, h463, h477, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h10, h466, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h0, hlam, p481_0]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [hlam, p481_0]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h11, h2, h463, h477, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h0, h11, h2, h463, h477, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h0, h10, h466, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h1, hlam, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h4, hlam, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [hlam, p481_0]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h11, h463, h477, h5, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h0, h10, h4, h466, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h2, hlam, p481_0]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h5, hlam, p481_0]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h7, hlam, p481_0]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [hlam, p481_0]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h10, h466, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h3, hlam, p481_0]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h6, hlam, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h8, hlam, p481_0]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [h9, hlam, p481_1]
                    · have p481_0 := h481c.1
                      have p481_1 := h481c.2.1
                      have p481_2 := h481c.2.2.1
                      have p481_3 := h481c.2.2.2
                      linarith only [hlam, p481_0]
                  · linarith only [h11, h463, h475, h477, h480, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h11, h463, h477, h479, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h11, h463, h474, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h510 | h510
      · linarith only [h10, h11, h510, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h512 | h512
        · linarith only [h10, h463, h512, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h514 | h514
          · rcases m.htr 2 3 4 (by decide) (by decide) with h515 | h515
            · linarith only [h0, h10, h463, h510, h515, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h517 | h517
              · linarith only [h0, h10, h11, h4, h512, h515, h517, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h519 | h519
                · rcases m.htr 3 4 5 (by decide) (by decide) with h520 | h520
                  · rcases h0bigk with h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [hlam, p521_0]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h4, h463, h515, h519, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h463, h515, h519, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h2, h514, hc01, hc45, hlam, hphi, ht0b, ht5b, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h463, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h0, hlam, p521_0]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [hlam, p521_0]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h463, h515, h519, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h0, h463, h5, h519, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h0, h463, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h1, hlam, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h4, hlam, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [hlam, p521_0]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h463, h5, h519, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h0, h4, h463, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h2, hlam, p521_0]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h5, hlam, p521_0]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h7, hlam, p521_0]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [hlam, p521_0]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h463, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h3, hlam, p521_0]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h6, hlam, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h8, hlam, p521_0]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [h9, hlam, p521_1]
                    · have p521_0 := h521c.1
                      have p521_1 := h521c.2.1
                      have p521_2 := h521c.2.2.1
                      have p521_3 := h521c.2.2.2
                      linarith only [hlam, p521_0]
                  · linarith only [h10, h463, h515, h519, h520, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h10, h11, h514, h519, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h549 | h549
            · linarith only [h0, h10, h463, h549, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h551 | h551
              · linarith only [h0, h10, h11, h4, h514, h551, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h553 | h553
                · linarith only [h0, h10, h11, h4, h514, h549, h553, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h10, h11, h4, h553, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

end R2N4
