import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6988000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s6_x0_x0_x0_x1 (m : N7Model)
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h648 | h648
  · rcases m.htr 1 2 5 (by decide) (by decide) with h649 | h649
    · rcases m.htr 1 3 4 (by decide) (by decide) with h650 | h650
      · rcases m.htr 1 4 5 (by decide) (by decide) with h651 | h651
        · rcases m.htr 2 3 4 (by decide) (by decide) with h652 | h652
          · rcases m.htr 2 3 5 (by decide) (by decide) with h653 | h653
            · rcases m.htr 2 4 5 (by decide) (by decide) with h654 | h654
              · linarith only [h0, h10, h4, h648, h654, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h10, h4, h648, h651, h654, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h648, h651, h653, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h10, h4, h648, h651, h652, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h659 | h659
          · rcases m.htr 2 3 5 (by decide) (by decide) with h660 | h660
            · rcases m.htr 2 4 5 (by decide) (by decide) with h661 | h661
              · linarith only [h10, h648, h651, h661, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h663 | h663
                · linarith only [h648, h651, h659, h663, hlam]
                · rcases h0bigk with h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [hlam, p665_0]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h10, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h10, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h648, h651, h659, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h648, h651, h659, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h0, hlam, p665_0]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [hlam, p665_0]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h648, h651, h659, h8, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h0, h648, h651, h659, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h0, h648, h651, h659, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h1, hlam, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h4, hlam, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [hlam, p665_0]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h0, h4, h648, h651, h659, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h0, h4, h648, h651, h659, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h2, hlam, p665_0]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h5, hlam, p665_0]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h7, hlam, p665_0]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [hlam, p665_0]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h648, h651, h659, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h3, hlam, p665_0]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h6, hlam, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h8, hlam, p665_0]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [h9, hlam, p665_1]
                  · have p665_0 := h665c.1
                    have p665_1 := h665c.2.1
                    have p665_2 := h665c.2.2.1
                    have p665_3 := h665c.2.2.2
                    linarith only [hlam, p665_0]
            · linarith only [h0, h10, h4, h648, h659, h660, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h4, h648, h659, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h648, h650, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h694 | h694
      · rcases m.htr 1 4 5 (by decide) (by decide) with h695 | h695
        · linarith only [h648, h649, h695, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h697 | h697
          · rcases m.htr 2 3 5 (by decide) (by decide) with h698 | h698
            · rcases m.htr 2 4 5 (by decide) (by decide) with h699 | h699
              · linarith only [h6, h648, h649, h695, h699, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h701 | h701
                · linarith only [h648, h649, h697, h699, h701, hlam]
                · rcases h0bigk with h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [hlam, p703_0]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h1, h10, h648, h697, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h3, h648, h649, h697, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h3, h648, h649, h697, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h0, hlam, p703_0]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [hlam, p703_0]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h1, h10, h648, h697, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h0, h3, h648, h649, h697, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h0, h3, h648, h649, h697, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h1, hlam, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h4, hlam, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [hlam, p703_0]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h6, h648, h649, h697, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h0, h4, h6, h648, h649, h697, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h2, hlam, p703_0]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h5, hlam, p703_0]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h7, hlam, p703_0]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [hlam, p703_0]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h6, h648, h649, h697, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h3, hlam, p703_0]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h6, hlam, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h8, hlam, p703_0]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [h9, hlam, p703_1]
                  · have p703_0 := h703c.1
                    have p703_1 := h703c.2.1
                    have p703_2 := h703c.2.2.1
                    have p703_3 := h703c.2.2.2
                    linarith only [hlam, p703_0]
            · linarith only [h0, h10, h4, h648, h697, h698, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h4, h648, h697, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h648, h694, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h732 | h732
    · rcases m.htr 1 3 4 (by decide) (by decide) with h733 | h733
      · rcases m.htr 1 4 5 (by decide) (by decide) with h734 | h734
        · rcases m.htr 2 3 4 (by decide) (by decide) with h735 | h735
          · rcases m.htr 2 3 5 (by decide) (by decide) with h736 | h736
            · rcases m.htr 2 4 5 (by decide) (by decide) with h737 | h737
              · rcases m.htr 3 4 5 (by decide) (by decide) with h738 | h738
                · rcases h0bigk with h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [hlam, p739_0]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p739_1]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h1, h733, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p739_1]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h2, h648, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p739_1]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    rcases p739_3 (m.d 0 1) (by simp) with h744 | h744
                    · rcases p739_3 (m.d 0 2) (by simp) with h745 | h745
                      · linarith only [h0, h745, hlam]
                      · linarith only [h6, h745, hlam]
                    · linarith only [h3, h744, hlam]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h0, hlam, p739_0]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [hlam, p739_0]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h5, h648, h7, h732, h736, h738, hc02, hc45, hlam, hphi, ht0b, ht5b, p739_1]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h0, h5, h648, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p739_1]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    rcases p739_3 (m.d 0 1) (by simp) with h753 | h753
                    · rcases p739_3 (m.d 0 2) (by simp) with h754 | h754
                      · rcases p739_3 (m.d 0 3) (by simp) with h755 | h755
                        · linarith only [h4, h755, hlam]
                        · linarith only [h755, h8, hlam]
                      · linarith only [h6, h754, hlam]
                    · linarith only [h3, h753, hlam]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h1, hlam, p739_1]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h4, hlam, p739_1]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [hlam, p739_0]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h5, h648, h732, h736, h738, hc03, hc45, hlam, hphi, ht0b, ht5b, p739_1]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    rcases p739_3 (m.d 0 1) (by simp) with h764 | h764
                    · rcases p739_3 (m.d 0 2) (by simp) with h765 | h765
                      · rcases p739_3 (m.d 0 3) (by simp) with h766 | h766
                        · rcases p739_3 (m.d 0 4) (by simp) with h767 | h767
                          · linarith only [h7, h767, hlam]
                          · linarith only [h767, h9, hlam]
                        · linarith only [h766, h8, hlam]
                      · linarith only [h6, h765, hlam]
                    · linarith only [h3, h764, hlam]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h2, hlam, p739_0]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h5, hlam, p739_0]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h7, hlam, p739_0]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [hlam, p739_0]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    rcases p739_3 (m.d 0 1) (by simp) with h777 | h777
                    · rcases p739_3 (m.d 0 2) (by simp) with h778 | h778
                      · rcases p739_3 (m.d 0 3) (by simp) with h779 | h779
                        · rcases p739_3 (m.d 0 4) (by simp) with h780 | h780
                          · rcases p739_3 (m.d 0 5) (by simp) with h781 | h781
                            · linarith only [h781, h9, hlam]
                            · rcases h0emin with h783 | h783 | h783 | h783 | h783
                              · rcases h2bigk with h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c | h784c
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [hlam, p784_0]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  rcases p784_3 (m.d 0 2) (by simp) with h786 | h786
                                  · rcases p784_3 (m.d 1 2) (by simp) with h787 | h787
                                    · linarith only [h0, h787, hlam]
                                    · rcases p784_3 (m.d 2 3) (by simp) with h789 | h789
                                      · linarith only [h4, h789, hlam]
                                      · linarith only [h10, h789, hlam]
                                  · linarith only [h0, h786, hlam]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h0, h648, h732, h735, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p784_1]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h0, h648, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p784_1]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h4, h648, h732, h735, hlam, p784_2]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h0, hlam, p784_0]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [hlam, p784_0]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h10, hlam, p784_0]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h648, hlam, p784_0]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h4, h648, h735, h736, h738, hc02, hc45, hlam, hphi, ht0b, ht5b, p784_1]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h4, hlam, p784_0]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h0, h4, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p784_1]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [hlam, p784_0]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h0, h4, h648, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p784_1]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  rcases p784_3 (m.d 0 2) (by simp) with h805 | h805
                                  · rcases p784_3 (m.d 1 2) (by simp) with h806 | h806
                                    · linarith only [h10, h806, hlam]
                                    · linarith only [h732, h806, hlam]
                                  · linarith only [h6, h805, hlam]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h5, hlam, p784_0]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h0, h5, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p784_1]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h735, hlam, p784_1]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [hlam, p784_0]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  rcases p784_3 (m.d 0 2) (by simp) with h814 | h814
                                  · rcases p784_3 (m.d 1 2) (by simp) with h815 | h815
                                    · linarith only [h648, h815, hlam]
                                    · linarith only [h732, h815, hlam]
                                  · linarith only [h6, h814, hlam]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h6, hlam, p784_0]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h732, hlam, p784_0]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h736, hlam, p784_1]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [h737, hlam, p784_0]
                                · have p784_0 := h784c.1
                                  have p784_1 := h784c.2.1
                                  have p784_2 := h784c.2.2.1
                                  have p784_3 := h784c.2.2.2
                                  linarith only [hlam, p784_0]
                              · rcases h2bigk with h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [hlam, p824_0]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  rcases p824_3 (m.d 0 2) (by simp) with h826 | h826
                                  · rcases p824_3 (m.d 1 2) (by simp) with h827 | h827
                                    · linarith only [h0, h827, hlam]
                                    · rcases p824_3 (m.d 2 3) (by simp) with h829 | h829
                                      · linarith only [h4, h829, hlam]
                                      · linarith only [h10, h829, hlam]
                                  · linarith only [h0, h826, hlam]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h0, h10, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p824_1]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h0, h648, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p824_1]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h10, h4, h732, hlam, p824_2]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h0, hlam, p824_0]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [hlam, p824_0]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h10, hlam, p824_0]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h648, hlam, p824_0]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h10, h4, h736, h738, hc02, hc45, hlam, hphi, ht0b, ht5b, p824_1]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h4, hlam, p824_0]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h0, h4, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p824_1]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [hlam, p824_0]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h0, h4, h648, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p824_1]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  rcases p824_3 (m.d 0 2) (by simp) with h845 | h845
                                  · rcases p824_3 (m.d 1 2) (by simp) with h846 | h846
                                    · linarith only [h10, h846, hlam]
                                    · linarith only [h732, h846, hlam]
                                  · linarith only [h6, h845, hlam]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h5, hlam, p824_0]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h0, h5, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p824_1]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h735, hlam, p824_1]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [hlam, p824_0]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  rcases p824_3 (m.d 0 2) (by simp) with h854 | h854
                                  · rcases p824_3 (m.d 1 2) (by simp) with h855 | h855
                                    · linarith only [h648, h855, hlam]
                                    · linarith only [h732, h855, hlam]
                                  · linarith only [h6, h854, hlam]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h6, hlam, p824_0]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h732, hlam, p824_0]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h736, hlam, p824_1]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [h737, hlam, p824_0]
                                · have p824_0 := h824c.1
                                  have p824_1 := h824c.2.1
                                  have p824_2 := h824c.2.2.1
                                  have p824_3 := h824c.2.2.2
                                  linarith only [hlam, p824_0]
                              · rcases h2bigk with h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [hlam, p864_0]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  rcases p864_3 (m.d 0 2) (by simp) with h866 | h866
                                  · rcases p864_3 (m.d 1 2) (by simp) with h867 | h867
                                    · linarith only [h0, h867, hlam]
                                    · rcases p864_3 (m.d 2 3) (by simp) with h869 | h869
                                      · linarith only [h4, h869, hlam]
                                      · linarith only [h10, h869, hlam]
                                  · linarith only [h0, h866, hlam]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h0, h10, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p864_1]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h0, h648, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p864_1]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h10, h4, h732, hlam, p864_2]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h0, hlam, p864_0]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [hlam, p864_0]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h10, hlam, p864_0]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h648, hlam, p864_0]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h10, h4, h736, h738, hc02, hc45, hlam, hphi, ht0b, ht5b, p864_1]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h4, hlam, p864_0]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h0, h4, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p864_1]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [hlam, p864_0]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h0, h4, h648, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p864_1]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  rcases p864_3 (m.d 0 2) (by simp) with h885 | h885
                                  · rcases p864_3 (m.d 1 2) (by simp) with h886 | h886
                                    · linarith only [h10, h886, hlam]
                                    · linarith only [h732, h886, hlam]
                                  · linarith only [h6, h885, hlam]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h5, hlam, p864_0]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h0, h5, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p864_1]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h735, hlam, p864_1]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [hlam, p864_0]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  rcases p864_3 (m.d 0 2) (by simp) with h894 | h894
                                  · rcases p864_3 (m.d 1 2) (by simp) with h895 | h895
                                    · linarith only [h648, h895, hlam]
                                    · linarith only [h732, h895, hlam]
                                  · linarith only [h6, h894, hlam]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h6, hlam, p864_0]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h732, hlam, p864_0]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h736, hlam, p864_1]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [h737, hlam, p864_0]
                                · have p864_0 := h864c.1
                                  have p864_1 := h864c.2.1
                                  have p864_2 := h864c.2.2.1
                                  have p864_3 := h864c.2.2.2
                                  linarith only [hlam, p864_0]
                              · rcases h2bigk with h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [hlam, p904_0]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  rcases p904_3 (m.d 0 2) (by simp) with h906 | h906
                                  · rcases p904_3 (m.d 1 2) (by simp) with h907 | h907
                                    · linarith only [h0, h907, hlam]
                                    · rcases p904_3 (m.d 2 3) (by simp) with h909 | h909
                                      · linarith only [h4, h909, hlam]
                                      · linarith only [h10, h909, hlam]
                                  · linarith only [h0, h906, hlam]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h0, h10, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p904_1]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h0, h648, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p904_1]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h10, h4, h732, hlam, p904_2]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h0, hlam, p904_0]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [hlam, p904_0]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h10, hlam, p904_0]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h648, hlam, p904_0]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h10, h4, h736, h738, hc02, hc45, hlam, hphi, ht0b, ht5b, p904_1]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h4, hlam, p904_0]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h0, h4, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p904_1]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [hlam, p904_0]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h0, h4, h648, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p904_1]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  rcases p904_3 (m.d 0 2) (by simp) with h925 | h925
                                  · rcases p904_3 (m.d 1 2) (by simp) with h926 | h926
                                    · linarith only [h10, h926, hlam]
                                    · linarith only [h732, h926, hlam]
                                  · linarith only [h6, h925, hlam]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h5, hlam, p904_0]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h0, h5, h732, h736, h738, hc01, hc45, hlam, hphi, ht0b, ht5b, p904_1]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h735, hlam, p904_1]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [hlam, p904_0]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  rcases p904_3 (m.d 0 2) (by simp) with h934 | h934
                                  · rcases p904_3 (m.d 1 2) (by simp) with h935 | h935
                                    · linarith only [h648, h935, hlam]
                                    · linarith only [h732, h935, hlam]
                                  · linarith only [h6, h934, hlam]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h6, hlam, p904_0]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h732, hlam, p904_0]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h736, hlam, p904_1]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [h737, hlam, p904_0]
                                · have p904_0 := h904c.1
                                  have p904_1 := h904c.2.1
                                  have p904_2 := h904c.2.2.1
                                  have p904_3 := h904c.2.2.2
                                  linarith only [hlam, p904_0]
                              · linarith only [h783, hc04, hlam, p739_1]
                          · linarith only [h780, h9, hlam]
                        · linarith only [h779, h8, hlam]
                      · linarith only [h6, h778, hlam]
                    · linarith only [h3, h777, hlam]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h3, hlam, p739_0]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h6, hlam, p739_1]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h8, hlam, p739_0]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [h9, hlam, p739_1]
                  · have p739_0 := h739c.1
                    have p739_1 := h739c.2.1
                    have p739_2 := h739c.2.2.1
                    have p739_3 := h739c.2.2.2
                    linarith only [hlam, p739_0]
                · linarith only [h0, h4, h648, h732, h735, h737, h738, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h4, h648, h7, h732, h737, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h648, h732, h735, h736, h8, hc03, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h10, h4, h7, h732, h735, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h648, h732, h734, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h959 | h959
        · rcases m.htr 2 3 4 (by decide) (by decide) with h960 | h960
          · linarith only [h0, h10, h4, h732, h733, h960, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h10, h4, h7, h732, h960, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h10, h732, h733, h959, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h964 | h964
      · rcases m.htr 1 4 5 (by decide) (by decide) with h965 | h965
        · rcases m.htr 2 3 4 (by decide) (by decide) with h966 | h966
          · rcases m.htr 2 3 5 (by decide) (by decide) with h967 | h967
            · rcases m.htr 2 4 5 (by decide) (by decide) with h968 | h968
              · rcases m.htr 3 4 5 (by decide) (by decide) with h969 | h969
                · rcases h0bigk with h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h4, h732, h966, h968, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h1, h964, h969, hc01, hc45, hlam, hphi, ht0b, ht5b, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h5, h732, h968, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h6, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h0, hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h1, h964, h969, hc02, hc45, hlam, hphi, ht0b, ht5b, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h0, h5, h732, h968, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h0, h6, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h1, hlam, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h4, hlam, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h5, h732, h968, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h0, h4, h6, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h2, hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h5, hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h7, hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h6, h732, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h3, hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h6, hlam, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h8, hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h9, hlam, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [hlam, p970_0]
                · rcases h0bigk with h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [hlam, p996_0]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h2, h4, h7, h965, h969, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h2, h7, h965, h969, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h2, h965, h969, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h6, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h0, hlam, p996_0]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [hlam, p996_0]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h2, h7, h965, h969, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h0, h2, h965, h969, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h0, h6, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h1, hlam, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h4, hlam, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [hlam, p996_0]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h5, h648, h965, h969, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h0, h4, h6, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h2, hlam, p996_0]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h5, hlam, p996_0]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h7, hlam, p996_0]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [hlam, p996_0]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h6, h732, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h3, hlam, p996_0]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h6, hlam, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h8, hlam, p996_0]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [h9, hlam, p996_1]
                  · have p996_0 := h996c.1
                    have p996_1 := h996c.2.1
                    have p996_2 := h996c.2.2.1
                    have p996_3 := h996c.2.2.2
                    linarith only [hlam, p996_0]
              · linarith only [h648, h965, h968, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1023 | h1023
              · linarith only [h1023, h966, h967, hlam]
              · linarith only [h1023, h648, h965, hlam]
          · linarith only [h1, h10, h964, h966, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1027 | h1027
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1028 | h1028
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1029 | h1029
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1030 | h1030
                · linarith only [h0, h10, h1030, h4, h648, h964, h965, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases h0bigk with h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [hlam, p1032_0]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h10, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h1029, h5, h648, h7, h965, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h1029, h5, h648, h965, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h648, h9, h965, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h0, hlam, p1032_0]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [hlam, p1032_0]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h1029, h5, h648, h7, h965, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h0, h1029, h5, h648, h965, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h0, h648, h9, h965, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h1, hlam, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h4, hlam, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [hlam, p1032_0]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h1029, h5, h648, h965, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h0, h4, h648, h9, h965, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h2, hlam, p1032_0]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h5, hlam, p1032_0]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h7, hlam, p1032_0]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [hlam, p1032_0]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h0, h4, h648, h7, h9, h965, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h3, hlam, p1032_0]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h6, hlam, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h8, hlam, p1032_0]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [h9, hlam, p1032_1]
                  · have p1032_0 := h1032c.1
                    have p1032_1 := h1032c.2.1
                    have p1032_2 := h1032c.2.2.1
                    have p1032_3 := h1032c.2.2.2
                    linarith only [hlam, p1032_0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1058 | h1058
                · linarith only [h1029, h1058, h648, h964, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases h0bigk with h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [hlam, p1060_0]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h10, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h5, h648, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h5, h648, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h1029, h648, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h0, hlam, p1060_0]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [hlam, p1060_0]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h5, h648, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h0, h5, h648, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h0, h1029, h648, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h1, hlam, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h4, hlam, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [hlam, p1060_0]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h5, h648, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h0, h1029, h4, h648, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h2, hlam, p1060_0]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h5, hlam, p1060_0]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h7, hlam, p1060_0]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [hlam, p1060_0]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h1029, h648, h9, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h3, hlam, p1060_0]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h6, hlam, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h8, hlam, p1060_0]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [h9, hlam, p1060_1]
                  · have p1060_0 := h1060c.1
                    have p1060_1 := h1060c.2.1
                    have p1060_2 := h1060c.2.2.1
                    have p1060_3 := h1060c.2.2.2
                    linarith only [hlam, p1060_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1086 | h1086
              · linarith only [h1027, h1028, h1086, h648, h965, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1088 | h1088
                · linarith only [h1086, h1088, h648, h964, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases h0bigk with h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [hlam, p1090_0]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h10, h1028, h1088, h4, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h10, h1028, h1088, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h10, h1028, h1088, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h10, h1028, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h0, hlam, p1090_0]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [hlam, p1090_0]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h10, h1028, h1088, h7, h9, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h0, h10, h1028, h1088, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h0, h10, h1028, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h1, hlam, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h4, hlam, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [hlam, p1090_0]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h10, h1028, h1088, h9, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h0, h10, h1028, h4, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h2, hlam, p1090_0]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h5, hlam, p1090_0]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h7, hlam, p1090_0]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [hlam, p1090_0]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h10, h1028, h8, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h3, hlam, p1090_0]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h6, hlam, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h8, hlam, p1090_0]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [h9, hlam, p1090_1]
                  · have p1090_0 := h1090c.1
                    have p1090_1 := h1090c.2.1
                    have p1090_2 := h1090c.2.2.1
                    have p1090_3 := h1090c.2.2.2
                    linarith only [hlam, p1090_0]
          · linarith only [h1, h10, h1027, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1117 | h1117
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1118 | h1118
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1119 | h1119
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1120 | h1120
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1121 | h1121
                · rcases h0bigk with h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1118, h4, h964, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1117, h2, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1117, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h6, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h0, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1117, h2, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h0, h1117, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h0, h6, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1, hlam, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h4, hlam, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1118, h5, h964, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h0, h4, h6, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h2, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h5, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h7, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h6, h732, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h3, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h6, hlam, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h8, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h9, hlam, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [hlam, p1122_0]
                · linarith only [h10, h1117, h1121, h2, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1117, h1118, h1120, h964, hlam]
            · linarith only [h10, h1118, h1119, h964, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1151 | h1151
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1152 | h1152
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1153 | h1153
                · rcases h0bigk with h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [hlam, p1154_0]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h1151, h4, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h1151, h4, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h1118, h1151, h7, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h6, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h0, hlam, p1154_0]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [hlam, p1154_0]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h1118, h1151, h7, h732, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h0, h1118, h1151, h7, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h0, h6, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h1, hlam, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h4, hlam, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [hlam, p1154_0]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h0, h1118, h1151, h4, h7, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h0, h4, h6, h732, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h2, hlam, p1154_0]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h5, hlam, p1154_0]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h7, hlam, p1154_0]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [hlam, p1154_0]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h6, h732, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h3, hlam, p1154_0]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h6, hlam, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h8, hlam, p1154_0]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [h9, hlam, p1154_1]
                  · have p1154_0 := h1154c.1
                    have p1154_1 := h1154c.2.1
                    have p1154_2 := h1154c.2.2.1
                    have p1154_3 := h1154c.2.2.2
                    linarith only [hlam, p1154_0]
                · linarith only [h1117, h1118, h1153, h648, hlam]
              · linarith only [h1117, h1118, h1151, h1152, h648, h732, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1182 | h1182
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1183 | h1183
                · rcases h0bigk with h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [hlam, p1184_0]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h1117, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h10, h1151, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h0, hlam, p1184_0]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [hlam, p1184_0]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h0, h1117, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h0, h10, h1151, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h1, hlam, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h4, hlam, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [hlam, p1184_0]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h10, h1151, h1182, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h0, h10, h1151, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h2, hlam, p1184_0]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h5, hlam, p1184_0]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h7, hlam, p1184_0]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [hlam, p1184_0]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h10, h1151, h8, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h3, hlam, p1184_0]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h6, hlam, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h8, hlam, p1184_0]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [h9, hlam, p1184_1]
                  · have p1184_0 := h1184c.1
                    have p1184_1 := h1184c.2.1
                    have p1184_2 := h1184c.2.2.1
                    have p1184_3 := h1184c.2.2.2
                    linarith only [hlam, p1184_0]
                · linarith only [h10, h1117, h1118, h1183, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1117, h1182, h648, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1212 | h1212
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1213 | h1213
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1214 | h1214
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1215 | h1215
                · linarith only [h0, h1117, h1212, h1215, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h10, h1212, h1214, h1215, h4, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1218 | h1218
                · linarith only [h1212, h1214, h1218, hlam]
                · rcases h0bigk with h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1213, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h10, h1212, h5, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h10, h1212, h1214, h9, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h0, hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1213, h4, hc02, hc35, hlam, hphi, ht0b, ht5b, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h0, h10, h1212, h5, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h0, h10, h1212, h1214, h9, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1, hlam, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h4, hlam, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h10, h1212, h5, h964, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h0, h10, h1212, h1214, h4, h9, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h2, hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h5, hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h7, hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h10, h1212, h1214, h9, h964, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h3, hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h6, hlam, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h8, hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h9, hlam, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [hlam, p1220_0]
            · linarith only [h10, h1212, h1213, h964, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1247 | h1247
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1248 | h1248
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1249 | h1249
                · linarith only [h0, h10, h1117, h1212, h1247, h1249, h4, h7, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h1212, h1247, h1248, h1249, h6, hc02, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h1212, h1247, h1248, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1253 | h1253
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1254 | h1254
                · rcases h0bigk with h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [hlam, p1255_0]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h10, h1117, h1212, h1253, h7, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h10, h1117, h1253, h5, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h10, h1117, h9, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h0, hlam, p1255_0]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [hlam, p1255_0]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h10, h1117, h1212, h1253, h7, h964, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h0, h10, h1117, h1212, h1253, h7, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h0, h10, h1117, h9, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h1, hlam, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h4, hlam, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [hlam, p1255_0]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h10, h1117, h1212, h1253, h7, h964, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h0, h10, h1117, h4, h9, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h2, hlam, p1255_0]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h5, hlam, p1255_0]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h7, hlam, p1255_0]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [hlam, p1255_0]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h0, h10, h1117, h4, h7, h9, h964, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h3, hlam, p1255_0]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h6, hlam, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h8, hlam, p1255_0]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [h9, hlam, p1255_1]
                  · have p1255_0 := h1255c.1
                    have p1255_1 := h1255c.2.1
                    have p1255_2 := h1255c.2.2.1
                    have p1255_3 := h1255c.2.2.2
                    linarith only [hlam, p1255_0]
                · linarith only [h1212, h1253, h1254, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1282 | h1282
                · linarith only [h0, h1253, h1282, h4, h648, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h10, h1212, h1282, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
