import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_19S0
import Jsp000404.R1LeavesN7_19S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5556000 in
theorem r1l7_21_14_H_I_L_I_s4_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h567 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h756 | h756
  · rcases m.htr 1 3 4 (by decide) (by decide) with h757 | h757
    · rcases m.htr 1 3 5 (by decide) (by decide) with h758 | h758
      · rcases m.htr 1 4 5 (by decide) (by decide) with h759 | h759
        · rcases m.htr 2 3 4 (by decide) (by decide) with h760 | h760
          · rcases m.htr 2 4 5 (by decide) (by decide) with h761 | h761
            · rcases m.htr 3 4 5 (by decide) (by decide) with h762 | h762
              · rcases h1bigk with h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [hlam, p763_0]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h756, h761, hc01, hc45, hlam, hphi, ht0b, ht5b, p763_1]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h757, h762, hc01, hc45, hlam, hphi, ht0b, ht5b, p763_1]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h567, h756, h761, hc01, hc45, hlam, hphi, ht0b, ht5b, p763_1]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  rcases p763_3 (m.d 0 1) (by simp) with h768 | h768
                  · rcases p763_3 (m.d 1 2) (by simp) with h769 | h769
                    · linarith only [h0, h769, hlam]
                    · linarith only [h756, h769, hlam]
                  · linarith only [h768, hlam, p763_0]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h0, hlam, p763_0]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [hlam, p763_0]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h7, hlam, p763_1]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h567, hlam, p763_1]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h567, h760, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p763_1]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h1, hlam, p763_0]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p763_1]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [hlam, p763_0]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h1, h567, h756, hc01, hc25, hlam, hphi, ht0b, ht5b, p763_1]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h1, h758, hc01, hc35, hlam, hphi, ht0b, ht5b, p763_1]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h2, hlam, p763_0]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h756, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p763_1]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h757, hlam, p763_1]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [hlam, p763_0]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h0, h4, h567, h758, hc01, hc35, hlam, hphi, ht0b, ht5b, p763_1]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h3, hlam, p763_0]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h756, hlam, p763_0]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h758, hlam, p763_0]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [h759, hlam, p763_0]
                · have p763_0 := h763c.1
                  have p763_1 := h763c.2.1
                  have p763_2 := h763c.2.2.1
                  have p763_3 := h763c.2.2.2
                  linarith only [hlam, p763_0]
              · linarith only [h0, h4, h567, h756, h761, h762, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h4, h567, h6, h756, h761, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h1, h5, h7, h756, h760, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h567, h756, h759, hlam]
      · linarith only [h7, h756, h758, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h798 | h798
      · rcases m.htr 1 4 5 (by decide) (by decide) with h799 | h799
        · rcases m.htr 2 3 4 (by decide) (by decide) with h800 | h800
          · rcases m.htr 2 4 5 (by decide) (by decide) with h801 | h801
            · rcases m.htr 3 4 5 (by decide) (by decide) with h802 | h802
              · rcases h1bigk with h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h756, hc01, hc25, hlam, hphi, ht0b, ht5b, p803_1]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h7, h756, h801, hc01, hc45, hlam, hphi, ht0b, ht5b, p803_1]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h7, h756, h757, h801, hc01, hc45, hlam, hphi, ht0b, ht5b, p803_1]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  rcases p803_3 (m.d 0 1) (by simp) with h808 | h808
                  · rcases p803_3 (m.d 1 2) (by simp) with h809 | h809
                    · linarith only [h0, h809, hlam]
                    · linarith only [h756, h809, hlam]
                  · linarith only [h808, hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h0, hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h7, hlam, p803_1]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h567, hlam, p803_1]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h7, h757, h800, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p803_1]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h1, hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h757, h800, hc12, hc23, hlam, hphi, p803_1]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h757, hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h756, h757, h800, h801, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p803_1]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h2, hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h756, h757, h800, h801, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p803_1]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h757, h800, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p803_1]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h756, h757, h800, h801, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p803_1]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h3, hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h756, hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h798, hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [h799, hlam, p803_0]
                · have p803_0 := h803c.1
                  have p803_1 := h803c.2.1
                  have p803_2 := h803c.2.2.1
                  have p803_3 := h803c.2.2.2
                  linarith only [hlam, p803_0]
              · linarith only [h0, h4, h567, h756, h757, h801, h802, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h4, h567, h6, h756, h801, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h1, h5, h7, h756, h800, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h7, h756, h757, h799, hlam]
      · linarith only [h7, h756, h798, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h838 | h838
    · rcases m.htr 1 3 5 (by decide) (by decide) with h839 | h839
      · rcases m.htr 1 4 5 (by decide) (by decide) with h840 | h840
        · rcases m.htr 2 3 4 (by decide) (by decide) with h841 | h841
          · rcases m.htr 2 4 5 (by decide) (by decide) with h842 | h842
            · rcases m.htr 3 4 5 (by decide) (by decide) with h843 | h843
              · rcases h1bigk with h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [hlam, p844_0]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  rcases p844_3 (m.d 0 1) (by simp) with h846 | h846
                  · rcases p844_3 (m.d 1 2) (by simp) with h847 | h847
                    · linarith only [h847, hlam, p844_0]
                    · rcases p844_3 (m.d 1 3) (by simp) with h849 | h849
                      · linarith only [h1, h849, hlam]
                      · linarith only [h7, h849, hlam]
                  · linarith only [h846, hlam, p844_0]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h838, h843, hc01, hc45, hlam, hphi, ht0b, ht5b, p844_1]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h838, h843, hc01, hc45, hlam, hphi, ht0b, ht5b, p844_1]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  rcases p844_3 (m.d 0 1) (by simp) with h855 | h855
                  · rcases p844_3 (m.d 1 2) (by simp) with h856 | h856
                    · linarith only [h0, h856, hlam]
                    · rcases p844_3 (m.d 1 3) (by simp) with h858 | h858
                      · linarith only [h1, h858, hlam]
                      · linarith only [h839, h858, hlam]
                  · linarith only [h855, hlam, p844_0]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h0, hlam, p844_0]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [hlam, p844_0]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h7, hlam, p844_1]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h567, hlam, p844_1]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h756, hlam, p844_1]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h1, hlam, p844_0]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p844_1]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [hlam, p844_0]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h1, h838, h843, hc01, hc45, hlam, hphi, ht0b, ht5b, p844_1]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p844_1]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h2, hlam, p844_0]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p844_1]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h838, hlam, p844_1]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [hlam, p844_0]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h0, h4, h567, h756, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p844_1]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h3, hlam, p844_0]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p844_1]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h839, hlam, p844_0]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [h840, hlam, p844_0]
                · have p844_0 := h844c.1
                  have p844_1 := h844c.2.1
                  have p844_2 := h844c.2.2.1
                  have p844_3 := h844c.2.2.2
                  linarith only [hlam, p844_0]
              · rcases h1bigk with h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [hlam, p882_0]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  rcases p882_3 (m.d 0 1) (by simp) with h884 | h884
                  · rcases p882_3 (m.d 1 2) (by simp) with h885 | h885
                    · linarith only [h885, hlam, p882_0]
                    · rcases p882_3 (m.d 1 3) (by simp) with h887 | h887
                      · linarith only [h1, h887, hlam]
                      · linarith only [h7, h887, hlam]
                  · linarith only [h884, hlam, p882_0]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h838, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h840, hc01, hc45, hlam, hphi, ht0b, ht5b, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h840, h843, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h0, hlam, p882_0]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [hlam, p882_0]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h7, hlam, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h567, hlam, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h756, hlam, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h1, hlam, p882_0]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [hlam, p882_0]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h1, h840, h843, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h2, hlam, p882_0]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h838, hlam, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [hlam, p882_0]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h0, h4, h567, h756, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h3, hlam, p882_0]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p882_1]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h839, hlam, p882_0]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [h840, hlam, p882_0]
                · have p882_0 := h882c.1
                  have p882_1 := h882c.2.1
                  have p882_2 := h882c.2.2.1
                  have p882_3 := h882c.2.2.2
                  linarith only [hlam, p882_0]
            · linarith only [h567, h840, h842, hlam]
          · linarith only [h7, h838, h841, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h916 | h916
          · rcases m.htr 2 4 5 (by decide) (by decide) with h917 | h917
            · rcases m.htr 3 4 5 (by decide) (by decide) with h918 | h918
              · linarith only [h838, h840, h918, hlam]
              · rcases h1bigk with h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  rcases p920_3 (m.d 0 1) (by simp) with h922 | h922
                  · rcases p920_3 (m.d 1 2) (by simp) with h923 | h923
                    · linarith only [h923, hlam, p920_0]
                    · rcases p920_3 (m.d 1 3) (by simp) with h925 | h925
                      · linarith only [h1, h925, hlam]
                      · linarith only [h7, h925, hlam]
                  · linarith only [h922, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h838, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  rcases p920_3 (m.d 0 1) (by simp) with h930 | h930
                  · rcases p920_3 (m.d 1 2) (by simp) with h931 | h931
                    · linarith only [h0, h931, hlam]
                    · rcases p920_3 (m.d 1 3) (by simp) with h933 | h933
                      · linarith only [h1, h933, hlam]
                      · linarith only [h838, h933, hlam]
                  · linarith only [h930, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  rcases p920_3 (m.d 0 1) (by simp) with h937 | h937
                  · rcases p920_3 (m.d 1 2) (by simp) with h938 | h938
                    · linarith only [h0, h938, hlam]
                    · rcases p920_3 (m.d 1 3) (by simp) with h940 | h940
                      · linarith only [h1, h940, hlam]
                      · linarith only [h839, h940, hlam]
                  · linarith only [h937, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h0, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h7, hlam, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h567, hlam, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h756, hlam, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h1, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h1, h567, h840, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h2, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h838, hlam, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h840, hlam, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h3, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h839, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h0, h4, h840, h917, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [hlam, p920_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h964 | h964
              · linarith only [h567, h917, h964, hc12, hc34, hlam, hphi, ht23]
              · rcases h1bigk with h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [hlam, p966_0]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  rcases p966_3 (m.d 0 1) (by simp) with h968 | h968
                  · rcases p966_3 (m.d 1 2) (by simp) with h969 | h969
                    · linarith only [h969, hlam, p966_0]
                    · rcases p966_3 (m.d 1 3) (by simp) with h971 | h971
                      · linarith only [h1, h971, hlam]
                      · linarith only [h7, h971, hlam]
                  · linarith only [h968, hlam, p966_0]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h838, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p966_1]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  rcases p966_3 (m.d 0 1) (by simp) with h976 | h976
                  · rcases p966_3 (m.d 1 2) (by simp) with h977 | h977
                    · linarith only [h0, h977, hlam]
                    · rcases p966_3 (m.d 1 3) (by simp) with h979 | h979
                      · linarith only [h1, h979, hlam]
                      · linarith only [h838, h979, hlam]
                  · linarith only [h976, hlam, p966_0]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  rcases p966_3 (m.d 0 1) (by simp) with h983 | h983
                  · rcases p966_3 (m.d 1 2) (by simp) with h984 | h984
                    · linarith only [h0, h984, hlam]
                    · rcases p966_3 (m.d 1 3) (by simp) with h986 | h986
                      · linarith only [h1, h986, hlam]
                      · linarith only [h839, h986, hlam]
                  · linarith only [h983, hlam, p966_0]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h0, hlam, p966_0]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [hlam, p966_0]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h7, hlam, p966_1]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h567, hlam, p966_1]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h756, hlam, p966_1]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h1, hlam, p966_0]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p966_1]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [hlam, p966_0]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h1, h567, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p966_1]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p966_1]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h2, hlam, p966_0]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p966_1]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h838, hlam, p966_1]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [hlam, p966_0]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h840, hlam, p966_1]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h3, hlam, p966_0]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p966_1]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h839, hlam, p966_0]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [h756, h917, hc14, hc45, hlam, hphi, p966_1]
                · have p966_0 := h966c.1
                  have p966_1 := h966c.2.1
                  have p966_2 := h966c.2.2.1
                  have p966_3 := h966c.2.2.2
                  linarith only [hlam, p966_0]
          · linarith only [h7, h838, h916, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1011 | h1011
        · linarith only [h1011, h838, h839, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1013 | h1013
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1014 | h1014
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1015 | h1015
              · linarith only [h1011, h1015, h838, h839, hlam]
              · linarith only [h0, h1014, h1015, h4, h838, h839, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1018 | h1018
              · linarith only [h1, h1014, h1018, h838, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases h1bigk with h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  rcases p1020_3 (m.d 0 1) (by simp) with h1022 | h1022
                  · rcases p1020_3 (m.d 1 2) (by simp) with h1023 | h1023
                    · linarith only [h1023, hlam, p1020_0]
                    · rcases p1020_3 (m.d 1 3) (by simp) with h1025 | h1025
                      · linarith only [h1, h1025, hlam]
                      · linarith only [h1025, h7, hlam]
                  · linarith only [h1022, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h838, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  rcases p1020_3 (m.d 0 1) (by simp) with h1030 | h1030
                  · rcases p1020_3 (m.d 1 2) (by simp) with h1031 | h1031
                    · linarith only [h0, h1031, hlam]
                    · rcases p1020_3 (m.d 1 3) (by simp) with h1033 | h1033
                      · linarith only [h1, h1033, hlam]
                      · linarith only [h1033, h838, hlam]
                  · linarith only [h1030, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h838, h839, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h0, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h7, hlam, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h567, hlam, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h756, hlam, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h839, hlam, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h2, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h838, hlam, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1011, hlam, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h3, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1014, h4, h6, h756, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h0, h1014, h4, h567, h6, h756, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [hlam, p1020_0]
          · linarith only [h1, h1013, h7, h838, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1059 | h1059
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1060 | h1060
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1061 | h1061
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1062 | h1062
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1063 | h1063
              · rcases h1bigk with h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  rcases p1064_3 (m.d 0 1) (by simp) with h1066 | h1066
                  · rcases p1064_3 (m.d 1 2) (by simp) with h1067 | h1067
                    · linarith only [h1067, hlam, p1064_0]
                    · rcases p1064_3 (m.d 1 3) (by simp) with h1069 | h1069
                      · linarith only [h1, h1069, hlam]
                      · linarith only [h1069, h7, hlam]
                  · linarith only [h1066, hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h1059, hc01, hc35, hlam, hphi, ht0b, ht5b, p1064_1]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h1059, h1063, h838, hc01, hc45, hlam, hphi, ht0b, ht5b, p1064_1]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  rcases p1064_3 (m.d 0 1) (by simp) with h1075 | h1075
                  · rcases p1064_3 (m.d 1 2) (by simp) with h1076 | h1076
                    · linarith only [h0, h1076, hlam]
                    · rcases p1064_3 (m.d 1 3) (by simp) with h1078 | h1078
                      · linarith only [h1, h1078, hlam]
                      · linarith only [h1059, h1078, hlam]
                  · linarith only [h1075, hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h0, hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h7, hlam, p1064_1]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h567, hlam, p1064_1]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h756, hlam, p1064_1]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h1, hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h1061, h4, h838, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h838, hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h1061, h838, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1064_1]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h2, hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h1061, h838, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1064_1]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h1061, h756, h838, hc12, hc23, hlam, hphi, p1064_1]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h3, hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h1059, hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [h1060, hlam, p1064_0]
                · have p1064_0 := h1064c.1
                  have p1064_1 := h1064c.2.1
                  have p1064_2 := h1064c.2.2.1
                  have p1064_3 := h1064c.2.2.2
                  linarith only [hlam, p1064_0]
              · linarith only [h0, h1059, h1063, h4, h6, h838, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h1059, h1060, h1061, h1062, h838, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1104 | h1104
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1105 | h1105
              · rcases h1bigk with h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  rcases p1106_3 (m.d 0 1) (by simp) with h1108 | h1108
                  · rcases p1106_3 (m.d 1 2) (by simp) with h1109 | h1109
                    · linarith only [h1109, hlam, p1106_0]
                    · rcases p1106_3 (m.d 1 3) (by simp) with h1111 | h1111
                      · linarith only [h1, h1111, hlam]
                      · linarith only [h1111, h7, hlam]
                  · linarith only [h1108, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1059, hc01, hc35, hlam, hphi, ht0b, ht5b, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1059, h1105, h838, hc01, hc45, hlam, hphi, ht0b, ht5b, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  rcases p1106_3 (m.d 0 1) (by simp) with h1117 | h1117
                  · rcases p1106_3 (m.d 1 2) (by simp) with h1118 | h1118
                    · linarith only [h0, h1118, hlam]
                    · rcases p1106_3 (m.d 1 3) (by simp) with h1120 | h1120
                      · linarith only [h1, h1120, hlam]
                      · linarith only [h1059, h1120, hlam]
                  · linarith only [h1117, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h0, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h7, hlam, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h567, hlam, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h756, hlam, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h838, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1, h1061, h5, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h2, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1, h1061, h5, h567, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1, h1061, h5, h567, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1, h1061, h5, h567, h756, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h3, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1059, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1060, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [hlam, p1106_0]
              · linarith only [h0, h1061, h1105, h4, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h1060, h1104, h567, hlam]
        · linarith only [h1059, h1060, h838, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1147 | h1147
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1148 | h1148
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1149 | h1149
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1150 | h1150
              · rcases h1bigk with h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  rcases p1151_3 (m.d 0 1) (by simp) with h1153 | h1153
                  · rcases p1151_3 (m.d 1 2) (by simp) with h1154 | h1154
                    · linarith only [h1154, hlam, p1151_0]
                    · rcases p1151_3 (m.d 1 3) (by simp) with h1156 | h1156
                      · linarith only [h1, h1156, hlam]
                      · linarith only [h1156, h7, hlam]
                  · linarith only [h1153, hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  rcases p1151_3 (m.d 0 1) (by simp) with h1160 | h1160
                  · rcases p1151_3 (m.d 1 2) (by simp) with h1161 | h1161
                    · linarith only [h0, h1161, hlam]
                    · rcases p1151_3 (m.d 1 3) (by simp) with h1163 | h1163
                      · linarith only [h1163, hlam, p1151_0]
                      · rcases p1151_3 (m.d 1 4) (by simp) with h1165 | h1165
                        · linarith only [h1165, h2, hlam]
                        · linarith only [h1165, h838, hlam]
                  · linarith only [h1160, hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h1147, hc01, hc45, hlam, hphi, ht0b, ht5b, p1151_1]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  rcases p1151_3 (m.d 0 1) (by simp) with h1170 | h1170
                  · rcases p1151_3 (m.d 1 2) (by simp) with h1171 | h1171
                    · linarith only [h0, h1171, hlam]
                    · rcases p1151_3 (m.d 1 3) (by simp) with h1173 | h1173
                      · linarith only [h1, h1173, hlam]
                      · rcases p1151_3 (m.d 1 4) (by simp) with h1175 | h1175
                        · linarith only [h1175, h2, hlam]
                        · linarith only [h1147, h1175, hlam]
                  · linarith only [h1170, hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h0, hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h7, hlam, p1151_1]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h567, hlam, p1151_1]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h756, hlam, p1151_1]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h1, hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h1059, h1148, h1150, hc12, hc23, hlam, hphi, p1151_1]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h838, hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h1059, hlam, p1151_1]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h2, hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1151_1]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h1148, h838, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1151_1]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h1059, h1148, h7, h838, hc12, hc23, hlam, hphi, p1151_1]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h3, hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1151_1]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h1059, h1148, h1150, h7, hc12, hc23, hlam, hphi, p1151_1]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [h1147, hlam, p1151_0]
                · have p1151_0 := h1151c.1
                  have p1151_1 := h1151c.2.1
                  have p1151_2 := h1151c.2.2.1
                  have p1151_3 := h1151c.2.2.2
                  linarith only [hlam, p1151_0]
              · linarith only [h1147, h1150, h838, hlam]
            · linarith only [h1147, h1149, h567, h838, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1201 | h1201
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1202 | h1202
              · rcases h1bigk with h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  rcases p1203_3 (m.d 0 1) (by simp) with h1205 | h1205
                  · rcases p1203_3 (m.d 1 2) (by simp) with h1206 | h1206
                    · linarith only [h1206, hlam, p1203_0]
                    · rcases p1203_3 (m.d 1 3) (by simp) with h1208 | h1208
                      · linarith only [h1, h1208, hlam]
                      · linarith only [h1208, h7, hlam]
                  · linarith only [h1205, hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  rcases p1203_3 (m.d 0 1) (by simp) with h1212 | h1212
                  · rcases p1203_3 (m.d 1 2) (by simp) with h1213 | h1213
                    · linarith only [h0, h1213, hlam]
                    · rcases p1203_3 (m.d 1 3) (by simp) with h1215 | h1215
                      · linarith only [h1215, hlam, p1203_0]
                      · rcases p1203_3 (m.d 1 4) (by simp) with h1217 | h1217
                        · linarith only [h1217, h2, hlam]
                        · linarith only [h1217, h838, hlam]
                  · linarith only [h1212, hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h1147, hc01, hc45, hlam, hphi, ht0b, ht5b, p1203_1]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  rcases p1203_3 (m.d 0 1) (by simp) with h1222 | h1222
                  · rcases p1203_3 (m.d 1 2) (by simp) with h1223 | h1223
                    · linarith only [h0, h1223, hlam]
                    · rcases p1203_3 (m.d 1 3) (by simp) with h1225 | h1225
                      · linarith only [h1, h1225, hlam]
                      · rcases p1203_3 (m.d 1 4) (by simp) with h1227 | h1227
                        · linarith only [h1227, h2, hlam]
                        · linarith only [h1147, h1227, hlam]
                  · linarith only [h1222, hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h0, hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h7, hlam, p1203_1]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h567, hlam, p1203_1]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h756, hlam, p1203_1]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h1, hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h1059, hc12, hc35, hlam, hphi, ht23, p1203_1]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h838, hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h1059, hlam, p1203_1]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h2, hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1203_1]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h1, h1148, h5, h567, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1203_1]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h1, h1148, h5, h567, hc01, hc15, hlam, hphi, ht0b, ht5b, p1203_1]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h3, hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1203_1]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h1, h1148, h1201, h5, h7, h756, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1203_1]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [h1147, hlam, p1203_0]
                · have p1203_0 := h1203c.1
                  have p1203_1 := h1203c.2.1
                  have p1203_2 := h1203c.2.2.1
                  have p1203_3 := h1203c.2.2.2
                  linarith only [hlam, p1203_0]
              · linarith only [h0, h1148, h1202, h4, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h1147, h1201, h567, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1253 | h1253
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1254 | h1254
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1255 | h1255
              · linarith only [h1147, h1253, h1255, h7, h838, hc12, hc23, hlam, hphi]
              · linarith only [h1254, h1255, h7, h838, hc12, hc24, hlam, hphi]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1258 | h1258
              · linarith only [h1253, h1254, h1258, hlam]
              · rcases h1bigk with h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c | h1260c
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  rcases p1260_3 (m.d 0 1) (by simp) with h1262 | h1262
                  · rcases p1260_3 (m.d 1 2) (by simp) with h1263 | h1263
                    · linarith only [h1263, hlam, p1260_0]
                    · rcases p1260_3 (m.d 1 3) (by simp) with h1265 | h1265
                      · linarith only [h1, h1265, hlam]
                      · linarith only [h1265, h7, hlam]
                  · linarith only [h1262, hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  rcases p1260_3 (m.d 0 1) (by simp) with h1269 | h1269
                  · rcases p1260_3 (m.d 1 2) (by simp) with h1270 | h1270
                    · linarith only [h0, h1270, hlam]
                    · rcases p1260_3 (m.d 1 3) (by simp) with h1272 | h1272
                      · linarith only [h1272, hlam, p1260_0]
                      · rcases p1260_3 (m.d 1 4) (by simp) with h1274 | h1274
                        · linarith only [h1274, h2, hlam]
                        · linarith only [h1274, h838, hlam]
                  · linarith only [h1269, hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  rcases p1260_3 (m.d 0 1) (by simp) with h1278 | h1278
                  · rcases p1260_3 (m.d 1 2) (by simp) with h1279 | h1279
                    · linarith only [h0, h1279, hlam]
                    · rcases p1260_3 (m.d 1 3) (by simp) with h1281 | h1281
                      · linarith only [h1, h1281, hlam]
                      · rcases p1260_3 (m.d 1 4) (by simp) with h1283 | h1283
                        · linarith only [h1283, hlam, p1260_0]
                        · rcases p1260_3 (m.d 1 5) (by simp) with h1285 | h1285
                          · linarith only [h1285, h3, hlam]
                          · linarith only [h1147, h1285, hlam]
                  · linarith only [h1278, hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  rcases p1260_3 (m.d 0 1) (by simp) with h1289 | h1289
                  · rcases p1260_3 (m.d 1 2) (by simp) with h1290 | h1290
                    · linarith only [h0, h1290, hlam]
                    · rcases p1260_3 (m.d 1 3) (by simp) with h1292 | h1292
                      · linarith only [h1, h1292, hlam]
                      · rcases p1260_3 (m.d 1 4) (by simp) with h1294 | h1294
                        · linarith only [h1294, h2, hlam]
                        · rcases p1260_3 (m.d 1 5) (by simp) with h1296 | h1296
                          · linarith only [h1296, hlam, p1260_0]
                          · rcases h4bigk with h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [hlam, p1298_0]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              rcases p1298_3 (m.d 0 4) (by simp) with h1300 | h1300
                              · rcases p1298_3 (m.d 1 4) (by simp) with h1301 | h1301
                                · linarith only [h1301, h2, hlam]
                                · rcases p1298_3 (m.d 2 4) (by simp) with h1303 | h1303
                                  · linarith only [h1303, h4, hlam]
                                  · linarith only [h1303, h567, hlam]
                              · linarith only [h1300, h2, hlam]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              rcases p1298_3 (m.d 0 4) (by simp) with h1307 | h1307
                              · rcases p1298_3 (m.d 1 4) (by simp) with h1308 | h1308
                                · linarith only [h1308, h2, hlam]
                                · rcases p1298_3 (m.d 2 4) (by simp) with h1310 | h1310
                                  · linarith only [h1310, h4, hlam]
                                  · rcases p1298_3 (m.d 3 4) (by simp) with h1312 | h1312
                                    · linarith only [h1312, h5, hlam]
                                    · rcases p1298_3 (m.d 4 5) (by simp) with h1314 | h1314
                                      · linarith only [h1314, h6, hlam]
                                      · linarith only [h1254, h1314, hlam]
                              · linarith only [h1307, h4, hlam]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              rcases p1298_3 (m.d 0 4) (by simp) with h1318 | h1318
                              · rcases p1298_3 (m.d 1 4) (by simp) with h1319 | h1319
                                · linarith only [h1319, h2, hlam]
                                · rcases p1298_3 (m.d 2 4) (by simp) with h1321 | h1321
                                  · linarith only [h1321, h4, hlam]
                                  · linarith only [h1253, h1321, hlam]
                              · linarith only [h1318, h5, hlam]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h0, h1253, h1254, h4, h7, h838, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1298_1]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h2, hlam, p1298_0]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [hlam, p1298_0]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h567, hlam, p1298_1]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h838, hlam, p1298_1]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h1147, hlam, p1298_0]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h4, hlam, p1298_0]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h1254, hc14, hc45, hlam, hphi, p1298_1]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [hlam, p1298_0]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h0, h1254, h4, h6, h7, h838, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1298_1]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h1254, hlam, p1298_0]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h5, hlam, p1298_0]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h1253, h7, h838, hc12, hc23, hlam, hphi, p1298_1]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h1253, hlam, p1298_0]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [hlam, p1298_0]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h1258, hlam, p1298_0]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h6, hlam, p1298_0]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              rcases p1298_3 (m.d 0 4) (by simp) with h1342 | h1342
                              · rcases p1298_3 (m.d 1 4) (by simp) with h1343 | h1343
                                · linarith only [h1343, hlam, p1298_0]
                                · rcases p1298_3 (m.d 2 4) (by simp) with h1345 | h1345
                                  · linarith only [h1254, h1345, hlam]
                                  · linarith only [h1345, h567, hlam]
                              · linarith only [h1342, h2, hlam]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h0, h4, h567, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1298_1]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [h0, h4, h6, h7, h838, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1298_1]
                            · have p1298_0 := h1298c.1
                              have p1298_1 := h1298c.2.1
                              have p1298_2 := h1298c.2.2.1
                              have p1298_3 := h1298c.2.2.2
                              linarith only [hlam, p1298_0]
                  · linarith only [h1289, hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h0, hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h7, hlam, p1260_1]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h567, hlam, p1260_1]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h756, hlam, p1260_1]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h1, hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h1253, h838, hc12, hc24, hlam, hphi, p1260_1]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h838, hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h1059, hlam, p1260_1]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h2, hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1260_1]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h0, h1253, h4, h838, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1260_1]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h1147, hlam, p1260_1]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h3, hlam, p1260_0]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1260_1]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h0, h1254, h4, h6, h7, h756, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1260_1]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [h0, h1254, h4, h6, h756, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1260_1]
                · have p1260_0 := h1260c.1
                  have p1260_1 := h1260c.2.1
                  have p1260_2 := h1260c.2.2.1
                  have p1260_3 := h1260c.2.2.2
                  linarith only [hlam, p1260_0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1373 | h1373
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1374 | h1374
              · rcases h1bigk with h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  rcases p1375_3 (m.d 0 1) (by simp) with h1377 | h1377
                  · rcases p1375_3 (m.d 1 2) (by simp) with h1378 | h1378
                    · linarith only [h1378, hlam, p1375_0]
                    · rcases p1375_3 (m.d 1 3) (by simp) with h1380 | h1380
                      · linarith only [h1, h1380, hlam]
                      · linarith only [h1380, h7, hlam]
                  · linarith only [h1377, hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  rcases p1375_3 (m.d 0 1) (by simp) with h1384 | h1384
                  · rcases p1375_3 (m.d 1 2) (by simp) with h1385 | h1385
                    · linarith only [h0, h1385, hlam]
                    · rcases p1375_3 (m.d 1 3) (by simp) with h1387 | h1387
                      · linarith only [h1387, hlam, p1375_0]
                      · rcases p1375_3 (m.d 1 4) (by simp) with h1389 | h1389
                        · linarith only [h1389, h2, hlam]
                        · linarith only [h1389, h838, hlam]
                  · linarith only [h1384, hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  rcases p1375_3 (m.d 0 1) (by simp) with h1393 | h1393
                  · rcases p1375_3 (m.d 1 2) (by simp) with h1394 | h1394
                    · linarith only [h0, h1394, hlam]
                    · rcases p1375_3 (m.d 1 3) (by simp) with h1396 | h1396
                      · linarith only [h1, h1396, hlam]
                      · rcases p1375_3 (m.d 1 4) (by simp) with h1398 | h1398
                        · linarith only [h1398, hlam, p1375_0]
                        · rcases p1375_3 (m.d 1 5) (by simp) with h1400 | h1400
                          · linarith only [h1400, h3, hlam]
                          · linarith only [h1147, h1400, hlam]
                  · linarith only [h1393, hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  rcases p1375_3 (m.d 0 1) (by simp) with h1404 | h1404
                  · rcases p1375_3 (m.d 1 2) (by simp) with h1405 | h1405
                    · linarith only [h0, h1405, hlam]
                    · rcases p1375_3 (m.d 1 3) (by simp) with h1407 | h1407
                      · linarith only [h1, h1407, hlam]
                      · rcases p1375_3 (m.d 1 4) (by simp) with h1409 | h1409
                        · linarith only [h1409, h2, hlam]
                        · rcases p1375_3 (m.d 1 5) (by simp) with h1411 | h1411
                          · linarith only [h1411, hlam, p1375_0]
                          · rcases h4bigk with h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              rcases p1413_3 (m.d 0 4) (by simp) with h1415 | h1415
                              · rcases p1413_3 (m.d 1 4) (by simp) with h1416 | h1416
                                · linarith only [h1416, h2, hlam]
                                · rcases p1413_3 (m.d 2 4) (by simp) with h1418 | h1418
                                  · linarith only [h1418, h4, hlam]
                                  · linarith only [h1418, h567, hlam]
                              · linarith only [h1415, h2, hlam]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1147, h1373, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h0, h1253, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              rcases p1413_3 (m.d 0 4) (by simp) with h1424 | h1424
                              · rcases p1413_3 (m.d 1 4) (by simp) with h1425 | h1425
                                · linarith only [h1425, h2, hlam]
                                · rcases p1413_3 (m.d 2 4) (by simp) with h1427 | h1427
                                  · linarith only [h1427, h4, hlam]
                                  · linarith only [h1373, h1427, hlam]
                              · linarith only [h1424, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h2, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h567, hlam, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h838, hlam, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1147, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h4, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              rcases p1413_3 (m.d 0 4) (by simp) with h1437 | h1437
                              · rcases p1413_3 (m.d 1 4) (by simp) with h1438 | h1438
                                · linarith only [h1438, h567, hlam]
                                · rcases p1413_3 (m.d 2 4) (by simp) with h1440 | h1440
                                  · rcases p1413_3 (m.d 3 4) (by simp) with h1441 | h1441
                                    · rcases p1413_3 (m.d 4 5) (by simp) with h1442 | h1442
                                      · linarith only [h1373, h1442, hlam]
                                      · linarith only [h1147, h1442, hlam]
                                    · linarith only [h1441, h838, hlam]
                                  · linarith only [h1440, h567, hlam]
                              · linarith only [h1437, h2, hlam]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1253, hlam, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1147, h7, h838, hc12, hc24, hlam, hphi, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h5, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              rcases p1413_3 (m.d 0 4) (by simp) with h1452 | h1452
                              · rcases p1413_3 (m.d 1 4) (by simp) with h1453 | h1453
                                · linarith only [h1453, h838, hlam]
                                · rcases p1413_3 (m.d 2 4) (by simp) with h1455 | h1455
                                  · linarith only [h1253, h1455, hlam]
                                  · linarith only [h1455, h567, hlam]
                              · linarith only [h1452, h2, hlam]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1, h5, h567, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1, h1147, h5, h7, h838, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h6, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1373, h7, h838, hc12, hc24, hlam, hphi, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1373, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1374, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [hlam, p1413_0]
                  · linarith only [h1404, hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h0, hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h7, hlam, p1375_1]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h567, hlam, p1375_1]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h756, hlam, p1375_1]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h1, hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1375_1]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h838, hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h1059, hlam, p1375_1]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h2, hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h0, h4, h567, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1375_1]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h0, h4, h567, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1375_1]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h1147, hlam, p1375_1]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h3, hlam, p1375_0]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1375_1]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h1, h1059, h1374, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1375_1]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [h0, h1147, h1373, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1375_1]
                · have p1375_0 := h1375c.1
                  have p1375_1 := h1375c.2.1
                  have p1375_2 := h1375c.2.2.1
                  have p1375_3 := h1375c.2.2.2
                  linarith only [hlam, p1375_0]
              · linarith only [h1253, h1373, h1374, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1489 | h1489
              · linarith only [h1, h1253, h1373, h1489, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1253, h1489, h7, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5556000 in
theorem r1l7_21_14_H_I_L_I_s4_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h567 | h567
  · exact r1l7_21_14_H_I_L_I_s4_x0_x0_x1_x0 m hb1 hb4 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h567
  · exact r1l7_21_14_H_I_L_I_s4_x0_x0_x1_x1 m hb1 hb4 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h567

set_option maxHeartbeats 5556000 in
theorem r1l7_21_14_H_I_L_I_s4_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
  · exact r1l7_21_14_H_I_L_I_s4_x0_x0_x0 m hb1 hb4 hg0 hg1 hg2 hg3 hg4 h5 h6 h7
  · exact r1l7_21_14_H_I_L_I_s4_x0_x0_x1 m hb1 hb4 hg0 hg1 hg2 hg3 hg4 h5 h6 h7

end R2N4
