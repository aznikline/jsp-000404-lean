import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_18S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0_x0_x0_x1 (m : N7Model)
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
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h454 | h454
  · rcases m.htr 1 2 5 (by decide) (by decide) with h455 | h455
    · rcases m.htr 1 3 4 (by decide) (by decide) with h456 | h456
      · rcases m.htr 1 3 5 (by decide) (by decide) with h457 | h457
        · rcases m.htr 2 3 4 (by decide) (by decide) with h458 | h458
          · rcases m.htr 2 3 5 (by decide) (by decide) with h459 | h459
            · rcases m.htr 2 4 5 (by decide) (by decide) with h460 | h460
              · linarith only [h0, h10, h4, h454, h460, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h462 | h462
                · linarith only [h458, h460, h462, hlam]
                · rcases h0bigk with h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [hlam, p464_0]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h10, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h1, h10, h455, h458, h460, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h458, h460, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h458, h460, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h0, hlam, p464_0]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [hlam, p464_0]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h10, h4, h455, h458, h460, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h0, h458, h460, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h0, h458, h460, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h1, hlam, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h4, hlam, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [hlam, p464_0]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h458, h460, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h0, h4, h458, h460, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h2, hlam, p464_0]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h5, hlam, p464_0]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h7, hlam, p464_0]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [hlam, p464_0]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h458, h460, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h3, hlam, p464_0]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h6, hlam, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h8, hlam, p464_0]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [h9, hlam, p464_1]
                  · have p464_0 := h464c.1
                    have p464_1 := h464c.2.1
                    have p464_2 := h464c.2.2.1
                    have p464_3 := h464c.2.2.2
                    linarith only [hlam, p464_0]
            · linarith only [h0, h10, h4, h454, h458, h459, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h4, h454, h458, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h10, h455, h457, hlam]
      · linarith only [h10, h454, h456, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h494 | h494
      · rcases m.htr 1 3 5 (by decide) (by decide) with h495 | h495
        · rcases m.htr 2 3 4 (by decide) (by decide) with h496 | h496
          · rcases m.htr 2 3 5 (by decide) (by decide) with h497 | h497
            · rcases m.htr 2 4 5 (by decide) (by decide) with h498 | h498
              · linarith only [h0, h454, h455, h498, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h500 | h500
                · linarith only [h454, h455, h496, h498, h500, hlam]
                · rcases h0bigk with h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h4, h454, h455, h496, h498, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h454, h455, h496, h498, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h454, h455, h496, h498, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h454, h455, h496, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h0, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h454, h455, h496, h498, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h0, h454, h455, h496, h498, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h0, h454, h455, h496, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h1, hlam, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h4, hlam, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h454, h455, h496, h498, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h0, h4, h454, h455, h496, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h2, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h5, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h7, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h454, h455, h496, h6, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h3, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h6, hlam, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h8, hlam, p502_0]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [h9, hlam, p502_1]
                  · have p502_0 := h502c.1
                    have p502_1 := h502c.2.1
                    have p502_2 := h502c.2.2.1
                    have p502_3 := h502c.2.2.2
                    linarith only [hlam, p502_0]
            · linarith only [h10, h495, h497, hlam]
          · linarith only [h0, h10, h4, h454, h496, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h530 | h530
          · rcases m.htr 2 3 5 (by decide) (by decide) with h531 | h531
            · linarith only [h0, h10, h4, h454, h495, h530, h531, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h454, h530, h531, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h4, h454, h530, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h454, h494, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h536 | h536
    · rcases m.htr 1 3 4 (by decide) (by decide) with h537 | h537
      · rcases m.htr 1 3 5 (by decide) (by decide) with h538 | h538
        · rcases m.htr 2 3 4 (by decide) (by decide) with h539 | h539
          · rcases m.htr 2 3 5 (by decide) (by decide) with h540 | h540
            · rcases m.htr 2 4 5 (by decide) (by decide) with h541 | h541
              · rcases m.htr 3 4 5 (by decide) (by decide) with h542 | h542
                · rcases h0bigk with h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [hlam, p543_0]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p543_1]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h1, h537, h542, hc01, hc45, hlam, hphi, ht0b, ht5b, p543_1]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h2, h454, h536, h540, h542, hc01, hc45, hlam, hphi, ht0b, ht5b, p543_1]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    rcases p543_3 (m.d 0 1) (by simp) with h548 | h548
                    · rcases p543_3 (m.d 0 2) (by simp) with h549 | h549
                      · linarith only [h0, h549, hlam]
                      · linarith only [h549, h6, hlam]
                    · linarith only [h3, h548, hlam]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h0, hlam, p543_0]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [hlam, p543_0]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h454, h5, h536, h540, h542, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p543_1]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h0, h454, h5, h536, h540, h542, hc01, hc45, hlam, hphi, ht0b, ht5b, p543_1]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    rcases p543_3 (m.d 0 1) (by simp) with h557 | h557
                    · rcases p543_3 (m.d 0 2) (by simp) with h558 | h558
                      · rcases p543_3 (m.d 0 3) (by simp) with h559 | h559
                        · linarith only [h4, h559, hlam]
                        · linarith only [h559, h8, hlam]
                      · linarith only [h558, h6, hlam]
                    · linarith only [h3, h557, hlam]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h1, hlam, p543_1]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h4, hlam, p543_1]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [hlam, p543_0]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h454, h5, h536, h540, h542, hc03, hc45, hlam, hphi, ht0b, ht5b, p543_1]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    rcases p543_3 (m.d 0 1) (by simp) with h568 | h568
                    · rcases p543_3 (m.d 0 2) (by simp) with h569 | h569
                      · rcases p543_3 (m.d 0 3) (by simp) with h570 | h570
                        · rcases p543_3 (m.d 0 4) (by simp) with h571 | h571
                          · linarith only [h571, h7, hlam]
                          · linarith only [h571, h9, hlam]
                        · linarith only [h570, h8, hlam]
                      · linarith only [h569, h6, hlam]
                    · linarith only [h3, h568, hlam]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h2, hlam, p543_0]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h5, hlam, p543_0]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h7, hlam, p543_0]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [hlam, p543_0]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    rcases p543_3 (m.d 0 1) (by simp) with h581 | h581
                    · rcases p543_3 (m.d 0 2) (by simp) with h582 | h582
                      · rcases p543_3 (m.d 0 3) (by simp) with h583 | h583
                        · rcases p543_3 (m.d 0 4) (by simp) with h584 | h584
                          · rcases p543_3 (m.d 0 5) (by simp) with h585 | h585
                            · linarith only [h585, h9, hlam]
                            · rcases h2bigk with h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                rcases p587_3 (m.d 0 2) (by simp) with h589 | h589
                                · rcases p587_3 (m.d 1 2) (by simp) with h590 | h590
                                  · linarith only [h0, h590, hlam]
                                  · rcases p587_3 (m.d 2 3) (by simp) with h592 | h592
                                    · linarith only [h4, h592, hlam]
                                    · linarith only [h10, h592, hlam]
                                · linarith only [h0, h589, hlam]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h0, h454, h536, h539, h540, h542, hc01, hc45, hlam, hphi, ht0b, ht5b, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h0, h454, h536, h540, h542, hc01, hc45, hlam, hphi, ht0b, ht5b, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h4, h454, h536, h539, hlam, p587_2]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h0, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h10, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h454, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h4, h454, h539, h540, h542, hc02, hc45, hlam, hphi, ht0b, ht5b, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h4, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h0, h4, h536, h540, h542, hc01, hc45, hlam, hphi, ht0b, ht5b, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h0, h4, h454, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                rcases p587_3 (m.d 0 2) (by simp) with h608 | h608
                                · rcases p587_3 (m.d 1 2) (by simp) with h609 | h609
                                  · linarith only [h10, h609, hlam]
                                  · linarith only [h536, h609, hlam]
                                · linarith only [h6, h608, hlam]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h5, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h0, h5, h536, h540, h542, hc01, hc45, hlam, hphi, ht0b, ht5b, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h539, hlam, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                rcases p587_3 (m.d 0 2) (by simp) with h617 | h617
                                · rcases p587_3 (m.d 1 2) (by simp) with h618 | h618
                                  · linarith only [h454, h618, hlam]
                                  · linarith only [h536, h618, hlam]
                                · linarith only [h6, h617, hlam]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h6, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h536, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h540, hlam, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h541, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [hlam, p587_0]
                          · linarith only [h584, h9, hlam]
                        · linarith only [h583, h8, hlam]
                      · linarith only [h582, h6, hlam]
                    · linarith only [h3, h581, hlam]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h3, hlam, p543_0]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h6, hlam, p543_1]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h8, hlam, p543_0]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [h9, hlam, p543_1]
                  · have p543_0 := h543c.1
                    have p543_1 := h543c.2.1
                    have p543_2 := h543c.2.2.1
                    have p543_3 := h543c.2.2.2
                    linarith only [hlam, p543_0]
                · linarith only [h0, h10, h4, h536, h541, h542, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h4, h454, h536, h541, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h4, h454, h536, h539, h540, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h10, h4, h536, h539, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h454, h536, h537, h538, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h641 | h641
        · rcases m.htr 2 3 4 (by decide) (by decide) with h642 | h642
          · linarith only [h0, h4, h537, h641, h642, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h10, h4, h536, h642, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h10, h536, h641, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h646 | h646
      · rcases m.htr 1 3 5 (by decide) (by decide) with h647 | h647
        · rcases m.htr 2 3 4 (by decide) (by decide) with h648 | h648
          · rcases m.htr 2 3 5 (by decide) (by decide) with h649 | h649
            · rcases m.htr 2 4 5 (by decide) (by decide) with h650 | h650
              · rcases m.htr 3 4 5 (by decide) (by decide) with h651 | h651
                · rcases h0bigk with h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [hlam, p652_0]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h1, h4, h646, h651, hc01, hc45, hlam, hphi, ht0b, ht5b, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h1, h646, h651, hc01, hc45, hlam, hphi, ht0b, ht5b, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h2, h646, h651, hc01, hc45, hlam, hphi, ht0b, ht5b, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h536, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h0, hlam, p652_0]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [hlam, p652_0]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h0, h1, h646, h651, hc01, hc45, hlam, hphi, ht0b, ht5b, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h0, h2, h646, h651, hc01, hc45, hlam, hphi, ht0b, ht5b, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h0, h536, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h1, hlam, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h4, hlam, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [hlam, p652_0]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h2, h646, h651, hc03, hc45, hlam, hphi, ht0b, ht5b, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h0, h4, h536, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h2, hlam, p652_0]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h5, hlam, p652_0]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h7, hlam, p652_0]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [hlam, p652_0]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h536, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h3, hlam, p652_0]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h6, hlam, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h8, hlam, p652_0]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [h9, hlam, p652_1]
                  · have p652_0 := h652c.1
                    have p652_1 := h652c.2.1
                    have p652_2 := h652c.2.2.1
                    have p652_3 := h652c.2.2.2
                    linarith only [hlam, p652_0]
                · rcases h0bigk with h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [hlam, p678_0]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h1, h647, hc01, hc35, hlam, hphi, ht0b, ht5b, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h5, h650, h651, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h651, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h0, hlam, p678_0]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [hlam, p678_0]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h4, h648, h650, h651, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h0, h5, h650, h651, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h0, h651, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h1, hlam, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h4, hlam, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [hlam, p678_0]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h5, h650, h651, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h0, h4, h651, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h2, hlam, p678_0]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h5, hlam, p678_0]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h7, hlam, p678_0]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [hlam, p678_0]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h651, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h3, hlam, p678_0]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h6, hlam, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h8, hlam, p678_0]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [h9, hlam, p678_1]
                  · have p678_0 := h678c.1
                    have p678_1 := h678c.2.1
                    have p678_2 := h678c.2.2.1
                    have p678_3 := h678c.2.2.2
                    linarith only [hlam, p678_0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h704 | h704
                · linarith only [h454, h646, h650, h704, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases h0bigk with h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [hlam, p706_0]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h10, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h454, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h454, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h454, h650, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h0, hlam, p706_0]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [hlam, p706_0]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h454, h5, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h0, h454, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h0, h454, h650, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h1, hlam, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h4, hlam, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [hlam, p706_0]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h454, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h0, h4, h454, h650, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h2, hlam, p706_0]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h5, hlam, p706_0]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h7, hlam, p706_0]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [hlam, p706_0]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h454, h650, h9, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h3, hlam, p706_0]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h6, hlam, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h8, hlam, p706_0]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [h9, hlam, p706_1]
                  · have p706_0 := h706c.1
                    have p706_1 := h706c.2.1
                    have p706_2 := h706c.2.2.1
                    have p706_3 := h706c.2.2.2
                    linarith only [hlam, p706_0]
            · linarith only [h1, h454, h647, h648, h649, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h10, h646, h648, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h734 | h734
          · rcases m.htr 2 3 5 (by decide) (by decide) with h735 | h735
            · linarith only [h0, h4, h646, h647, h735, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h737 | h737
              · linarith only [h734, h735, h737, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h739 | h739
                · linarith only [h454, h646, h737, h739, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases h0bigk with h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [hlam, p741_0]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h1, h4, h646, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h1, h646, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h454, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h454, h734, h735, h739, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h0, hlam, p741_0]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [hlam, p741_0]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h4, h454, h734, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h0, h454, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h0, h454, h734, h735, h739, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h1, hlam, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h4, hlam, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [hlam, p741_0]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h454, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h0, h4, h454, h734, h735, h739, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h2, hlam, p741_0]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h5, hlam, p741_0]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h7, hlam, p741_0]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [hlam, p741_0]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h454, h734, h735, h739, h9, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h3, hlam, p741_0]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h6, hlam, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h8, hlam, p741_0]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [h9, hlam, p741_1]
                  · have p741_0 := h741c.1
                    have p741_1 := h741c.2.1
                    have p741_2 := h741c.2.2.1
                    have p741_3 := h741c.2.2.2
                    linarith only [hlam, p741_0]
          · linarith only [h1, h10, h646, h734, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h768 | h768
        · rcases m.htr 2 3 4 (by decide) (by decide) with h769 | h769
          · linarith only [h0, h4, h646, h768, h769, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h771 | h771
            · rcases m.htr 2 4 5 (by decide) (by decide) with h772 | h772
              · rcases m.htr 3 4 5 (by decide) (by decide) with h773 | h773
                · rcases h0bigk with h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [hlam, p774_0]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h1, h4, h768, h773, hc01, hc45, hlam, hphi, ht0b, ht5b, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h1, h768, h773, hc01, hc45, hlam, hphi, ht0b, ht5b, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h536, h7, h769, h771, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h536, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h0, hlam, p774_0]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [hlam, p774_0]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h536, h7, h769, h771, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h0, h536, h7, h769, h771, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h0, h536, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h1, hlam, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h4, hlam, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [hlam, p774_0]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h0, h4, h536, h7, h769, h771, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h0, h4, h536, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h2, hlam, p774_0]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h5, hlam, p774_0]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h7, hlam, p774_0]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [hlam, p774_0]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h536, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h3, hlam, p774_0]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h6, hlam, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h8, hlam, p774_0]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [h9, hlam, p774_1]
                  · have p774_0 := h774c.1
                    have p774_1 := h774c.2.1
                    have p774_2 := h774c.2.2.1
                    have p774_3 := h774c.2.2.2
                    linarith only [hlam, p774_0]
                · linarith only [h536, h769, h771, h773, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h769, h771, h772, hlam]
            · linarith only [h1, h10, h768, h771, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h803 | h803
          · rcases m.htr 2 3 5 (by decide) (by decide) with h804 | h804
            · rcases m.htr 2 4 5 (by decide) (by decide) with h805 | h805
              · rcases m.htr 3 4 5 (by decide) (by decide) with h806 | h806
                · rcases h0bigk with h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [hlam, p807_0]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h4, h646, h803, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h4, h803, h806, hc01, hc45, hlam, hphi, ht0b, ht5b, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h7, h806, hc01, hc45, hlam, hphi, ht0b, ht5b, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h10, h6, h768, h804, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h0, hlam, p807_0]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [hlam, p807_0]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h0, h4, h803, h806, hc01, hc45, hlam, hphi, ht0b, ht5b, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h0, h7, h806, hc01, hc45, hlam, hphi, ht0b, ht5b, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h0, h10, h6, h768, h804, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h1, hlam, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h4, hlam, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [hlam, p807_0]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h0, h4, h7, h806, hc01, hc45, hlam, hphi, ht0b, ht5b, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h0, h10, h4, h6, h768, h804, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h2, hlam, p807_0]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h5, hlam, p807_0]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h7, hlam, p807_0]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [hlam, p807_0]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h10, h6, h768, h804, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h3, hlam, p807_0]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h6, hlam, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h8, hlam, p807_0]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [h9, hlam, p807_1]
                  · have p807_0 := h807c.1
                    have p807_1 := h807c.2.1
                    have p807_2 := h807c.2.2.1
                    have p807_3 := h807c.2.2.2
                    linarith only [hlam, p807_0]
                · linarith only [h10, h646, h803, h805, h806, hc12, hc23, hlam, hphi]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h834 | h834
                · linarith only [h803, h805, h834, hlam]
                · rcases h0bigk with h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [hlam, p836_0]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h10, h5, h646, h7, h803, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h10, h5, h646, h803, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h10, h646, h803, h805, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h0, hlam, p836_0]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [hlam, p836_0]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h10, h5, h646, h7, h803, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h0, h10, h5, h646, h803, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h0, h10, h646, h803, h805, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h1, hlam, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h4, hlam, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [hlam, p836_0]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h10, h5, h646, h803, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h0, h10, h4, h646, h803, h805, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h2, hlam, p836_0]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h5, hlam, p836_0]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h7, hlam, p836_0]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [hlam, p836_0]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h10, h646, h803, h805, h9, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h3, hlam, p836_0]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h6, hlam, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h8, hlam, p836_0]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [h9, hlam, p836_1]
                  · have p836_0 := h836c.1
                    have p836_1 := h836c.2.1
                    have p836_2 := h836c.2.2.1
                    have p836_3 := h836c.2.2.2
                    linarith only [hlam, p836_0]
            · linarith only [h0, h10, h4, h646, h8, h803, h804, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h863 | h863
            · linarith only [h10, h768, h803, h863, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h865 | h865
              · rcases m.htr 3 4 5 (by decide) (by decide) with h866 | h866
                · rcases h0bigk with h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [hlam, p867_0]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h5, h865, hc01, hc45, hlam, hphi, ht0b, ht5b, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h10, h8, h863, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h0, hlam, p867_0]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [hlam, p867_0]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h10, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h0, h5, h865, hc01, hc45, hlam, hphi, ht0b, ht5b, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h0, h10, h8, h863, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h1, hlam, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h4, hlam, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [hlam, p867_0]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h5, h865, hc03, hc45, hlam, hphi, ht0b, ht5b, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h0, h10, h4, h8, h863, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h2, hlam, p867_0]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h5, hlam, p867_0]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h7, hlam, p867_0]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [hlam, p867_0]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h10, h8, h863, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h3, hlam, p867_0]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h6, hlam, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h8, hlam, p867_0]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [h9, hlam, p867_1]
                  · have p867_0 := h867c.1
                    have p867_1 := h867c.2.1
                    have p867_2 := h867c.2.2.1
                    have p867_3 := h867c.2.2.2
                    linarith only [hlam, p867_0]
                · linarith only [h10, h803, h866, hc12, hc45, hlam, hphi, ht23, ht34]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h894 | h894
                · linarith only [h10, h803, h865, h894, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h10, h803, h894, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0_x0_x0 (m : N7Model)
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h10
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h10

end R2N4
