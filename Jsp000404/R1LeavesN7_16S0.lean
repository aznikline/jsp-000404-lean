import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5636000 in
theorem r1l7_21_15_H_I_L_I_s6_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
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
                      linarith only [h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h10, h17, hc01, hc35, hlam, hphi, ht0b, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h15, h16, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                    · have p24_0 := h24c.1
                      have p24_1 := h24c.2.1
                      have p24_2 := h24c.2.2.1
                      have p24_3 := h24c.2.2.2
                      linarith only [h15, h16, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
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
                      linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p24_1]
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
                      linarith only [h0, h10, h12, hc01, hc25, hlam, hphi, ht0b, ht5b, p24_1]
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
                      linarith only [h12, h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p24_1]
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
            · rcases m.htr 2 3 5 (by decide) (by decide) with h51 | h51
              · linarith only [h0, h10, h13, h16, h51, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                  · rcases h1bigk with h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h10, h13, h51, h54, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h13, h51, h54, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h11, h53, hc01, hc45, hlam, hphi, ht0b, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h14, h51, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
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
                      linarith only [h13, h51, h54, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h0, h13, h51, h54, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h0, h14, h51, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h1, hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h10, hlam, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h13, h51, h54, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h0, h10, h14, h51, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h2, hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h11, hlam, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h13, hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h14, h51, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h3, hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h12, hlam, p55_1]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h14, hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [h15, hlam, p55_0]
                    · have p55_0 := h55c.1
                      have p55_1 := h55c.2.1
                      have p55_2 := h55c.2.2.1
                      have p55_3 := h55c.2.2.2
                      linarith only [hlam, p55_0]
                  · linarith only [h0, h11, h53, h54, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h0, h10, h13, h53, h82, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h10, h13, h15, h16, h82, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
            · rcases m.htr 2 3 5 (by decide) (by decide) with h86 | h86
              · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                · linarith only [h0, h11, h15, h87, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                  · linarith only [h11, h15, h85, h89, hlam]
                  · rcases h1bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h13, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      rcases p91_3 (m.d 0 1) (by simp) with h95 | h95
                      · rcases p91_3 (m.d 1 2) (by simp) with h96 | h96
                        · linarith only [h0, h96, hlam]
                        · linarith only [h11, h96, hlam]
                      · linarith only [h95, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      rcases p91_3 (m.d 0 1) (by simp) with h100 | h100
                      · rcases p91_3 (m.d 1 2) (by simp) with h101 | h101
                        · linarith only [h0, h101, hlam]
                        · linarith only [h101, h12, hlam]
                      · linarith only [h100, hlam, p91_0]
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
                      linarith only [h10, h86, h89, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h0, h11, h85, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h0, h11, h15, h85, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h1, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h10, hlam, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h1, h11, h85, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h0, h10, h11, h15, h85, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h2, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h11, hlam, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h13, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h15, hlam, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h3, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h12, hlam, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h14, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h11, h3, h85, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hlam, p91_0]
              · linarith only [h0, h10, h14, h85, h86, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
              · linarith only [h0, h10, h126, h13, h85, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h128 | h128
                · linarith only [h128, h13, h15, h85, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
                  · linarith only [h13, h130, h15, hlam]
                  · rcases h1bigk with h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [hlam, p132_0]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h13, h85, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h13, h85, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h13, h15, h85, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h0, hlam, p132_0]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [hlam, p132_0]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h13, h85, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h0, h13, h85, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h1, hlam, p132_0]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h10, hlam, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [hlam, p132_0]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h13, h85, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h0, h10, h12, h128, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h2, hlam, p132_0]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h11, hlam, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h13, hlam, p132_0]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [hlam, p132_0]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h15, hlam, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h3, hlam, p132_0]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h12, hlam, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h14, hlam, p132_0]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [h13, h85, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p132_1]
                    · have p132_0 := h132c.1
                      have p132_1 := h132c.2.1
                      have p132_2 := h132c.2.2.1
                      have p132_3 := h132c.2.2.2
                      linarith only [hlam, p132_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
          · linarith only [h13, h14, h158, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
            · rcases m.htr 2 3 5 (by decide) (by decide) with h161 | h161
              · linarith only [h10, h14, h161, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h163 | h163
                · linarith only [h0, h11, h158, h163, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h165 | h165
                  · linarith only [h10, h14, h158, h160, h165, hlam]
                  · rcases h1bigk with h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [hlam, p167_0]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h10, h160, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h10, h160, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      rcases p167_3 (m.d 0 1) (by simp) with h171 | h171
                      · rcases p167_3 (m.d 1 2) (by simp) with h172 | h172
                        · linarith only [h0, h172, hlam]
                        · linarith only [h11, h172, hlam]
                      · linarith only [h171, hlam, p167_0]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h10, h14, h160, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h0, hlam, p167_0]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [hlam, p167_0]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h10, h160, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h0, h11, h160, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h0, h10, h14, h160, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h1, hlam, p167_0]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h10, hlam, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [hlam, p167_0]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h11, h14, h160, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h14, hlam, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h2, hlam, p167_0]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h11, hlam, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h13, hlam, p167_0]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [hlam, p167_0]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h158, hlam, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h3, hlam, p167_0]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h12, hlam, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [h11, h14, h160, h165, hc34, hc45, hlam, hphi, p167_1]
                    · have p167_0 := h167c.1
                      have p167_1 := h167c.2.1
                      have p167_2 := h167c.2.2.1
                      have p167_3 := h167c.2.2.2
                      linarith only [hlam, p167_0]
            · linarith only [h0, h13, h14, h160, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h198 | h198
        · rcases m.htr 1 4 5 (by decide) (by decide) with h199 | h199
          · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
            · linarith only [h10, h13, h200, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
              · rcases m.htr 2 4 5 (by decide) (by decide) with h203 | h203
                · rcases m.htr 3 4 5 (by decide) (by decide) with h204 | h204
                  · rcases h1bigk with h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h10, h202, h204, hc01, hc45, hlam, hphi, ht0b, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h10, h13, h202, h204, hc01, hc45, hlam, hphi, ht0b, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      rcases p205_3 (m.d 0 1) (by simp) with h210 | h210
                      · rcases p205_3 (m.d 1 2) (by simp) with h211 | h211
                        · linarith only [h0, h211, hlam]
                        · linarith only [h12, h211, hlam]
                      · linarith only [h210, hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h0, hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h10, h202, h204, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h0, h10, h13, h202, h204, hc01, hc45, hlam, hphi, ht0b, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h1, hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h10, hlam, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h13, hlam, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h12, h13, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h2, hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h11, hlam, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h0, h13, h198, h204, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h3, hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h12, hlam, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h198, hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h199, hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hlam, p205_0]
                  · linarith only [h0, h10, h13, h202, h204, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h13, h198, h199, h200, h202, h203, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h13, h198, h202, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h13, h198, h199, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h239 | h239
          · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
            · linarith only [h10, h13, h240, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h242 | h242
              · linarith only [h10, h198, h242, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h244 | h244
                · rcases m.htr 3 4 5 (by decide) (by decide) with h245 | h245
                  · rcases h1bigk with h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      rcases p246_3 (m.d 0 1) (by simp) with h249 | h249
                      · rcases p246_3 (m.d 1 2) (by simp) with h250 | h250
                        · linarith only [h0, h250, hlam]
                        · linarith only [h10, h250, hlam]
                      · linarith only [h249, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h11, h244, hc01, hc45, hlam, hphi, ht0b, ht5b, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      rcases p246_3 (m.d 0 1) (by simp) with h255 | h255
                      · rcases p246_3 (m.d 1 2) (by simp) with h256 | h256
                        · linarith only [h0, h256, hlam]
                        · linarith only [h12, h256, hlam]
                      · linarith only [h255, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h0, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h0, h11, h244, hc01, hc45, hlam, hphi, ht0b, ht5b, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h0, h10, h198, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h1, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h10, hlam, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h13, hlam, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h198, hlam, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h2, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h11, hlam, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h10, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h10, h13, h198, hc23, hc34, hlam, hphi, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h3, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h12, hlam, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h10, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h239, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [hlam, p246_0]
                  · linarith only [h0, h11, h13, h244, h245, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h281 | h281
                  · rcases h1bigk with h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      rcases p282_3 (m.d 0 1) (by simp) with h285 | h285
                      · rcases p282_3 (m.d 1 2) (by simp) with h286 | h286
                        · linarith only [h0, h286, hlam]
                        · linarith only [h10, h286, hlam]
                      · linarith only [h285, hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h239, h240, h244, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h239, h240, h244, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h0, hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h0, h239, h240, h244, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h0, h239, h240, h244, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h1, hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h10, hlam, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h13, hlam, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h198, hlam, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h2, hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h11, hlam, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h10, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h0, h13, h239, h240, h244, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h3, hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h12, hlam, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h10, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h239, hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [hlam, p282_0]
                  · linarith only [h13, h239, h281, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h313 | h313
            · linarith only [h10, h13, h313, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h315 | h315
              · linarith only [h10, h198, h315, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h317 | h317
                · linarith only [h0, h11, h13, h239, h317, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h319 | h319
                  · rcases h1bigk with h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      rcases p320_3 (m.d 0 1) (by simp) with h323 | h323
                      · rcases p320_3 (m.d 1 2) (by simp) with h324 | h324
                        · linarith only [h0, h324, hlam]
                        · linarith only [h10, h324, hlam]
                      · linarith only [h323, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      rcases p320_3 (m.d 0 1) (by simp) with h328 | h328
                      · rcases p320_3 (m.d 1 2) (by simp) with h329 | h329
                        · linarith only [h0, h329, hlam]
                        · linarith only [h11, h329, hlam]
                      · linarith only [h328, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      rcases p320_3 (m.d 0 1) (by simp) with h333 | h333
                      · rcases p320_3 (m.d 1 2) (by simp) with h334 | h334
                        · linarith only [h0, h334, hlam]
                        · linarith only [h12, h334, hlam]
                      · linarith only [h333, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h0, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h0, h10, h13, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h0, h10, h13, h239, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h1, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h10, hlam, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h13, hlam, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h198, hlam, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h2, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h11, hlam, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h10, h239, h319, h4, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h239, hlam, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h3, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h12, hlam, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h10, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h0, h239, h319, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [hlam, p320_0]
                  · rcases h1bigk with h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [hlam, p358_0]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      rcases p358_3 (m.d 0 1) (by simp) with h361 | h361
                      · rcases p358_3 (m.d 1 2) (by simp) with h362 | h362
                        · linarith only [h0, h362, hlam]
                        · linarith only [h10, h362, hlam]
                      · linarith only [h361, hlam, p358_0]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      rcases p358_3 (m.d 0 1) (by simp) with h366 | h366
                      · rcases p358_3 (m.d 1 2) (by simp) with h367 | h367
                        · linarith only [h0, h367, hlam]
                        · linarith only [h11, h367, hlam]
                      · linarith only [h366, hlam, p358_0]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      rcases p358_3 (m.d 0 1) (by simp) with h371 | h371
                      · rcases p358_3 (m.d 1 2) (by simp) with h372 | h372
                        · linarith only [h0, h372, hlam]
                        · linarith only [h12, h372, hlam]
                      · linarith only [h371, hlam, p358_0]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h0, hlam, p358_0]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [hlam, p358_0]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h0, h11, h313, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h1, hlam, p358_0]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h10, hlam, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [hlam, p358_0]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h13, hlam, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h198, hlam, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h2, hlam, p358_0]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h11, hlam, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h10, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [hlam, p358_0]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h239, hlam, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h3, hlam, p358_0]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h12, hlam, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h10, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [h198, h319, hc14, hc45, hlam, hphi, p358_1]
                    · have p358_0 := h358c.1
                      have p358_1 := h358c.2.1
                      have p358_2 := h358c.2.2.1
                      have p358_3 := h358c.2.2.2
                      linarith only [hlam, p358_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h396 | h396
      · rcases m.htr 1 3 5 (by decide) (by decide) with h397 | h397
        · linarith only [h10, h12, h397, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h399 | h399
          · linarith only [h11, h12, h399, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h401 | h401
            · linarith only [h0, h10, h12, h401, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h396, h397, h4, h401, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h404 | h404
        · linarith only [h11, h12, h396, h404, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h406 | h406
          · linarith only [h11, h12, h406, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
            · linarith only [h0, h10, h12, h396, h408, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h410 | h410
              · linarith only [h10, h12, h404, h410, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h412 | h412
                · linarith only [h0, h11, h12, h412, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h414 | h414
                  · linarith only [h11, h12, h408, h412, h414, hc23, hc34, hlam, hphi]
                  · rcases h1bigk with h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h11, h408, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      rcases p416_3 (m.d 0 1) (by simp) with h419 | h419
                      · rcases p416_3 (m.d 1 2) (by simp) with h420 | h420
                        · linarith only [h0, h420, hlam]
                        · linarith only [h10, h420, hlam]
                      · linarith only [h419, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      rcases p416_3 (m.d 0 1) (by simp) with h424 | h424
                      · rcases p416_3 (m.d 1 2) (by simp) with h425 | h425
                        · linarith only [h0, h425, hlam]
                        · linarith only [h11, h425, hlam]
                      · linarith only [h424, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h11, h12, h408, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h0, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h12, h4, h410, h414, h7, h9, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h0, h12, h4, h410, h414, h7, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h12, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h1, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h10, hlam, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h396, hlam, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h404, hlam, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h2, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h11, hlam, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h10, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h406, hlam, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h3, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h11, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h0, h10, h12, h4, h410, h414, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h0, h12, h4, h410, h414, h7, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [hlam, p416_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h450 | h450
    · rcases m.htr 1 3 4 (by decide) (by decide) with h451 | h451
      · linarith only [h10, h11, h451, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h453 | h453
        · rcases m.htr 1 4 5 (by decide) (by decide) with h454 | h454
          · rcases m.htr 2 3 4 (by decide) (by decide) with h455 | h455
            · linarith only [h0, h4, h451, h453, h455, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h457 | h457
              · linarith only [h0, h10, h11, h457, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h10, h11, h4, h453, h455, h457, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h10, h11, h453, h454, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h461 | h461
          · rcases m.htr 2 3 4 (by decide) (by decide) with h462 | h462
            · linarith only [h0, h10, h11, h462, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h464 | h464
              · linarith only [h0, h10, h11, h4, h453, h462, h464, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h466 | h466
                · rcases m.htr 3 4 5 (by decide) (by decide) with h467 | h467
                  · rcases h1bigk with h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [hlam, p468_0]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h450, hc01, hc25, hlam, hphi, ht0b, ht5b, p468_1]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      rcases p468_3 (m.d 0 1) (by simp) with h471 | h471
                      · rcases p468_3 (m.d 1 2) (by simp) with h472 | h472
                        · linarith only [h0, h472, hlam]
                        · linarith only [h10, h472, hlam]
                      · linarith only [h471, hlam, p468_0]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h11, h450, h464, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      rcases p468_3 (m.d 0 1) (by simp) with h477 | h477
                      · rcases p468_3 (m.d 1 2) (by simp) with h478 | h478
                        · linarith only [h0, h478, hlam]
                        · linarith only [h450, h478, hlam]
                      · linarith only [h477, hlam, p468_0]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h0, hlam, p468_0]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [hlam, p468_0]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h11, hlam, p468_0]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h0, h11, h4, h462, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p468_1]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h1, hlam, p468_0]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h10, hlam, p468_1]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [hlam, p468_0]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h451, hlam, p468_1]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h453, hlam, p468_1]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h2, hlam, p468_0]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h0, h11, h4, h462, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p468_1]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h0, h10, h11, h4, h462, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [hlam, p468_0]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h0, h11, h4, h450, h462, h464, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h3, hlam, p468_0]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h450, hlam, p468_1]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h10, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [h461, hlam, p468_0]
                    · have p468_0 := h468c.1
                      have p468_1 := h468c.2.1
                      have p468_2 := h468c.2.2.1
                      have p468_3 := h468c.2.2.2
                      linarith only [hlam, p468_0]
                  · linarith only [h0, h10, h11, h4, h462, h467, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h11, h450, h453, h461, h464, h466, hc23, hc35, hlam, hphi]
          · linarith only [h11, h450, h461, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h505 | h505
      · linarith only [h10, h11, h505, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h507 | h507
        · linarith only [h10, h450, h507, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h509 | h509
          · rcases m.htr 2 3 4 (by decide) (by decide) with h510 | h510
            · linarith only [h0, h10, h11, h5, h505, h510, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h512 | h512
              · linarith only [h10, h450, h507, h512, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h514 | h514
                · rcases m.htr 3 4 5 (by decide) (by decide) with h515 | h515
                  · rcases h1bigk with h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [hlam, p516_0]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p516_1]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      rcases p516_3 (m.d 0 1) (by simp) with h519 | h519
                      · rcases p516_3 (m.d 1 2) (by simp) with h520 | h520
                        · linarith only [h0, h520, hlam]
                        · linarith only [h10, h520, hlam]
                      · linarith only [h519, hlam, p516_0]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h10, h450, h509, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p516_1]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h10, h450, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p516_1]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h0, hlam, p516_0]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [hlam, p516_0]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h10, h4, h450, h510, h514, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p516_1]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h11, hlam, p516_0]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h450, hlam, p516_0]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h1, hlam, p516_0]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h10, hlam, p516_1]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [hlam, p516_0]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h505, hlam, p516_1]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h507, hlam, p516_1]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h2, hlam, p516_0]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p516_1]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h0, h10, h11, h4, h510, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p516_1]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [hlam, p516_0]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h0, h10, h11, h4, h450, h510, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p516_1]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h3, hlam, p516_0]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h10, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p516_1]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h0, h10, h4, h450, h510, h514, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p516_1]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [h509, hlam, p516_0]
                    · have p516_0 := h516c.1
                      have p516_1 := h516c.2.1
                      have p516_2 := h516c.2.2.1
                      have p516_3 := h516c.2.2.2
                      linarith only [hlam, p516_0]
                  · linarith only [h11, h509, h510, h515, hlam]
                · linarith only [h11, h509, h514, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h548 | h548
            · linarith only [h0, h10, h11, h5, h548, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h550 | h550
              · linarith only [h0, h10, h11, h4, h509, h550, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h552 | h552
                · linarith only [h0, h10, h11, h4, h509, h548, h552, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h10, h11, h4, h552, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

end R2N4
