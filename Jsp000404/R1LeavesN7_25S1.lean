import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 5 (by decide) (by decide) with h746 | h746
  · rcases m.htr 1 3 4 (by decide) (by decide) with h747 | h747
    · linarith only [h7, h747, h8, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h749 | h749
      · rcases m.htr 2 3 4 (by decide) (by decide) with h750 | h750
        · linarith only [h0, h2, h747, h749, h750, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h752 | h752
          · linarith only [h0, h2, h5, h7, h750, h752, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h2, h5, h7, h749, h750, h752, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h755 | h755
        · linarith only [h0, h3, h7, h755, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h757 | h757
          · linarith only [h0, h2, h5, h7, h749, h755, h757, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h759 | h759
            · rcases m.htr 3 4 5 (by decide) (by decide) with h760 | h760
              · rcases h2bigk with h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  rcases p761_3 (m.d 0 2) (by simp) with h763 | h763
                  · rcases p761_3 (m.d 1 2) (by simp) with h764 | h764
                    · linarith only [h0, h764, hlam]
                    · rcases p761_3 (m.d 2 3) (by simp) with h766 | h766
                      · linarith only [h2, h766, hlam]
                      · rcases p761_3 (m.d 2 4) (by simp) with h768 | h768
                        · linarith only [h3, h768, hlam]
                        · linarith only [h768, h8, hlam]
                  · linarith only [h0, h763, hlam]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h2, h5, h7, h755, h8, hlam, p761_2]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h0, h746, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p761_1]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h3, h746, h8, hlam, p761_2]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h0, hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h0, h3, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p761_1]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h8, hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h0, h3, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p761_1]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h2, hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h7, hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h755, hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h757, hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h3, hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h0, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p761_1]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  rcases p761_3 (m.d 0 2) (by simp) with h787 | h787
                  · rcases p761_3 (m.d 1 2) (by simp) with h788 | h788
                    · linarith only [h788, h8, hlam]
                    · linarith only [h7, h788, hlam]
                  · linarith only [h2, h787, hlam]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  rcases p761_3 (m.d 0 2) (by simp) with h793 | h793
                  · rcases p761_3 (m.d 1 2) (by simp) with h794 | h794
                    · linarith only [h794, h8, hlam]
                    · linarith only [h746, h794, hlam]
                  · linarith only [h4, h793, hlam]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h4, hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h746, hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h0, h746, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p761_1]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [h759, hlam, p761_0]
                · have p761_0 := h761c.1
                  have p761_1 := h761c.2.1
                  have p761_2 := h761c.2.2.1
                  have p761_3 := h761c.2.2.2
                  linarith only [hlam, p761_0]
              · linarith only [h7, h755, h760, h8, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h746, h757, h759, h8, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h805 | h805
    · linarith only [h7, h8, h805, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h807 | h807
      · linarith only [h7, h746, h807, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h809 | h809
        · linarith only [h7, h8, h805, h809, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h811 | h811
          · linarith only [h7, h746, h807, h811, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h813 | h813
            · rcases m.htr 3 4 5 (by decide) (by decide) with h814 | h814
              · rcases h2bigk with h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  rcases p815_3 (m.d 0 2) (by simp) with h817 | h817
                  · rcases p815_3 (m.d 1 2) (by simp) with h818 | h818
                    · linarith only [h0, h818, hlam]
                    · rcases p815_3 (m.d 2 3) (by simp) with h820 | h820
                      · linarith only [h2, h820, hlam]
                      · rcases p815_3 (m.d 2 4) (by simp) with h822 | h822
                        · linarith only [h3, h822, hlam]
                        · linarith only [h8, h822, hlam]
                  · linarith only [h0, h817, hlam]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h2, h5, h7, h746, h809, h813, hlam, p815_2]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h0, h7, h746, h813, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p815_1]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h0, h7, h746, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p815_1]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h0, hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h746, h809, h813, hc23, hc34, hlam, hphi, p815_1]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h8, hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h746, hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h2, hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h7, hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h809, hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h811, hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h3, hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h0, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p815_1]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  rcases p815_3 (m.d 0 2) (by simp) with h841 | h841
                  · rcases p815_3 (m.d 1 2) (by simp) with h842 | h842
                    · linarith only [h8, h842, hlam]
                    · linarith only [h7, h842, hlam]
                  · linarith only [h2, h841, hlam]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h0, h2, h5, h7, h746, h809, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p815_1]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h4, hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p815_1]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  rcases p815_3 (m.d 0 2) (by simp) with h850 | h850
                  · rcases p815_3 (m.d 1 2) (by simp) with h851 | h851
                    · linarith only [h746, h851, hlam]
                    · linarith only [h7, h851, hlam]
                  · linarith only [h2, h850, hlam]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [h813, hlam, p815_0]
                · have p815_0 := h815c.1
                  have p815_1 := h815c.2.1
                  have p815_2 := h815c.2.2.1
                  have p815_3 := h815c.2.2.2
                  linarith only [hlam, p815_0]
              · linarith only [h809, h813, h814, hlam]
            · linarith only [h7, h8, h813, hc23, hc45, hlam, hphi, ht34]

set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8

set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h859 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 5 (by decide) (by decide) with h860 | h860
  · rcases m.htr 1 3 4 (by decide) (by decide) with h861 | h861
    · rcases m.htr 1 3 5 (by decide) (by decide) with h862 | h862
      · rcases m.htr 2 3 4 (by decide) (by decide) with h863 | h863
        · rcases m.htr 2 3 5 (by decide) (by decide) with h864 | h864
          · rcases m.htr 2 4 5 (by decide) (by decide) with h865 | h865
            · linarith only [h0, h2, h7, h859, h865, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h867 | h867
              · linarith only [h863, h865, h867, hlam]
              · rcases h2bigk with h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [hlam, p869_0]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  rcases p869_3 (m.d 0 2) (by simp) with h871 | h871
                  · rcases p869_3 (m.d 1 2) (by simp) with h872 | h872
                    · linarith only [h0, h872, hlam]
                    · rcases p869_3 (m.d 2 3) (by simp) with h874 | h874
                      · linarith only [h2, h874, hlam]
                      · linarith only [h7, h874, hlam]
                  · linarith only [h0, h871, hlam]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h0, h7, h860, h865, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p869_1]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h2, h7, h860, h865, hlam, p869_2]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h2, h7, h860, hlam, p869_2]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h0, hlam, p869_0]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [hlam, p869_0]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h7, hlam, p869_0]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h0, h2, h7, h863, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p869_1]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h0, h2, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p869_1]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h2, hlam, p869_0]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h0, h2, h859, h863, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p869_1]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [hlam, p869_0]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  rcases p869_3 (m.d 0 2) (by simp) with h889 | h889
                  · rcases p869_3 (m.d 1 2) (by simp) with h890 | h890
                    · linarith only [h7, h890, hlam]
                    · linarith only [h859, h890, hlam]
                  · linarith only [h3, h889, hlam]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  rcases p869_3 (m.d 0 2) (by simp) with h894 | h894
                  · rcases p869_3 (m.d 1 2) (by simp) with h895 | h895
                    · linarith only [h7, h895, hlam]
                    · linarith only [h860, h895, hlam]
                  · linarith only [h4, h894, hlam]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h3, hlam, p869_0]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h859, hlam, p869_0]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h863, hlam, p869_1]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [hlam, p869_0]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h865, hlam, p869_1]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h4, hlam, p869_0]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h860, hlam, p869_0]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h864, hlam, p869_1]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [h0, h860, h863, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p869_1]
                · have p869_0 := h869c.1
                  have p869_1 := h869c.2.1
                  have p869_2 := h869c.2.2.1
                  have p869_3 := h869c.2.2.2
                  linarith only [hlam, p869_0]
          · linarith only [h0, h2, h6, h7, h860, h864, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h2, h5, h7, h859, h863, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h7, h860, h862, hlam]
    · linarith only [h7, h859, h861, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h913 | h913
    · rcases m.htr 1 3 5 (by decide) (by decide) with h914 | h914
      · rcases m.htr 2 3 4 (by decide) (by decide) with h915 | h915
        · rcases m.htr 2 3 5 (by decide) (by decide) with h916 | h916
          · rcases m.htr 2 4 5 (by decide) (by decide) with h917 | h917
            · linarith only [h0, h2, h859, h860, h916, h917, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h919 | h919
              · linarith only [h0, h2, h5, h859, h860, h917, h919, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases h2bigk with h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [hlam, p921_0]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  rcases p921_3 (m.d 0 2) (by simp) with h923 | h923
                  · rcases p921_3 (m.d 1 2) (by simp) with h924 | h924
                    · linarith only [h0, h924, hlam]
                    · rcases p921_3 (m.d 2 3) (by simp) with h926 | h926
                      · linarith only [h2, h926, hlam]
                      · linarith only [h7, h926, hlam]
                  · linarith only [h0, h923, hlam]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h0, h859, h860, h915, h916, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p921_1]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h2, h859, h860, h916, hlam, p921_2]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h0, h859, h860, h915, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p921_1]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h0, hlam, p921_0]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [hlam, p921_0]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h7, hlam, p921_0]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h860, h915, h917, hc34, hc45, hlam, hphi, p921_1]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h860, hlam, p921_0]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h2, hlam, p921_0]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h0, h2, h859, h915, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p921_1]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [hlam, p921_0]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  rcases p921_3 (m.d 0 2) (by simp) with h941 | h941
                  · rcases p921_3 (m.d 1 2) (by simp) with h942 | h942
                    · linarith only [h7, h942, hlam]
                    · linarith only [h859, h942, hlam]
                  · linarith only [h3, h941, hlam]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h0, h2, h859, h860, h915, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p921_1]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h3, hlam, p921_0]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h859, hlam, p921_0]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h915, hlam, p921_1]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [hlam, p921_0]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h917, hlam, p921_1]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h4, hlam, p921_0]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h0, h4, h859, h915, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p921_1]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [h916, hlam, p921_1]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  rcases p921_3 (m.d 0 2) (by simp) with h955 | h955
                  · rcases p921_3 (m.d 1 2) (by simp) with h956 | h956
                    · linarith only [h860, h956, hlam]
                    · linarith only [h859, h956, hlam]
                  · linarith only [h3, h955, hlam]
                · have p921_0 := h921c.1
                  have p921_1 := h921c.2.1
                  have p921_2 := h921c.2.2.1
                  have p921_3 := h921c.2.2.2
                  linarith only [hlam, p921_0]
          · linarith only [h0, h2, h6, h7, h859, h915, h916, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h2, h5, h7, h859, h915, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h963 | h963
        · rcases m.htr 2 3 5 (by decide) (by decide) with h964 | h964
          · linarith only [h0, h2, h7, h859, h914, h963, h964, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h2, h6, h7, h859, h963, h964, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h2, h5, h7, h859, h963, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h7, h859, h913, hlam]

set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h859 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h969 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 3 4 (by decide) (by decide) with h970 | h970
  · rcases m.htr 1 3 5 (by decide) (by decide) with h971 | h971
    · rcases m.htr 2 3 4 (by decide) (by decide) with h972 | h972
      · rcases m.htr 2 3 5 (by decide) (by decide) with h973 | h973
        · rcases m.htr 2 4 5 (by decide) (by decide) with h974 | h974
          · rcases m.htr 3 4 5 (by decide) (by decide) with h975 | h975
            · rcases h2bigk with h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                rcases p976_3 (m.d 0 2) (by simp) with h978 | h978
                · rcases p976_3 (m.d 1 2) (by simp) with h979 | h979
                  · linarith only [h0, h979, hlam]
                  · rcases p976_3 (m.d 2 3) (by simp) with h981 | h981
                    · linarith only [h2, h981, hlam]
                    · linarith only [h7, h981, hlam]
                · linarith only [h0, h978, hlam]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h0, h7, h969, h973, h975, hc01, hc45, hlam, hphi, ht0b, ht5b, p976_1]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h0, h859, h969, h973, h975, hc01, hc45, hlam, hphi, ht0b, ht5b, p976_1]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h3, h859, h969, hlam, p976_2]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h0, hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h7, hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h859, hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h0, h3, h859, hc01, hc25, hlam, hphi, ht0b, ht5b, p976_1]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h2, hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h0, h2, h969, hc01, hc25, hlam, hphi, ht0b, ht5b, p976_1]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h0, h2, h859, h969, hc01, hc25, hlam, hphi, ht0b, ht5b, p976_1]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                rcases p976_3 (m.d 0 2) (by simp) with h997 | h997
                · rcases p976_3 (m.d 1 2) (by simp) with h998 | h998
                  · linarith only [h7, h998, hlam]
                  · linarith only [h969, h998, hlam]
                · linarith only [h4, h997, hlam]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h3, hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h0, h3, h969, h973, h975, hc01, hc45, hlam, hphi, ht0b, ht5b, p976_1]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h972, hlam, p976_1]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                rcases p976_3 (m.d 0 2) (by simp) with h1006 | h1006
                · rcases p976_3 (m.d 1 2) (by simp) with h1007 | h1007
                  · linarith only [h1007, h859, hlam]
                  · linarith only [h1007, h969, hlam]
                · linarith only [h1006, h4, hlam]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h4, hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h969, hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h973, hlam, p976_1]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h974, hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hlam, p976_0]
            · linarith only [h0, h2, h7, h969, h974, h975, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h859, h969, h974, hlam]
        · linarith only [h0, h2, h6, h859, h969, h972, h973, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h0, h2, h5, h7, h969, h972, hc01, hc25, hlam, hphi, ht0b, ht5b]
    · linarith only [h7, h969, h971, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1021 | h1021
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1022 | h1022
      · linarith only [h0, h1021, h1022, h2, h970, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · linarith only [h0, h1022, h2, h5, h7, h969, hc01, hc25, hlam, hphi, ht0b, ht5b]
    · linarith only [h1021, h7, h969, hlam]

end R2N4
