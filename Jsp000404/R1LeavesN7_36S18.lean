import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2006 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2517 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2655 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2656 | h2656
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2657 | h2657
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2658 | h2658
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2659 | h2659
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2660 | h2660
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2661 | h2661
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2662 | h2662
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2663 | h2663
                · rcases h0bigk with h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [hlam, p2664_0]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h0, hlam, p2664_1]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2006, hlam, p2664_0]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2517, hlam, p2664_1]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2517, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p2664_1]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2655, hc02, hc15, hlam, hphi, ht0b, ht5b, p2664_1]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [hlam, p2664_0]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2659, hc02, hlam, hphi, ht0b, ht45, ht5b, p2664_1, u4ehi0]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2664_1, u4ehi0]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h0, h2661, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2664_1, u4ehi4]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2655, h2661, hc03, hlam, hphi, ht0b, ht45, ht5b, p2664_1, u4ehi4]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2656, hlam, p2664_1]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [hlam, p2664_0]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h0, h2656, h2659, h2663, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2664_1, u4ehi4]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h0, h2656, h2661, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2664_1, u4ehi4]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2655, h2661, hc04, hlam, hphi, ht0b, ht45, ht5b, p2664_1, u4ehi4]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2657, hlam, p2664_0]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2659, hlam, p2664_0]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [hlam, p2664_0]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h0, h2656, h2659, h2661, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2664_1, u4ehi4]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2655, hlam, p2664_0]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2658, hlam, p2664_1]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2660, hlam, p2664_0]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [h2661, hlam, p2664_1]
                  · have p2664_0 := h2664c.1
                    have p2664_1 := h2664c.2.1
                    have p2664_2 := h2664c.2.2.1
                    have p2664_3 := h2664c.2.2.2
                    linarith only [hlam, p2664_0]
                · linarith only [h0, h2655, h2662, h2663, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h2517, h2661, h2662, hlam]
            · linarith only [h2517, h2655, h2661, hlam]
          · linarith only [h2006, h2655, h2660, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2694 | h2694
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2695 | h2695
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2696 | h2696
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2697 | h2697
                · rcases h0bigk with h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [hlam, p2698_0]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h0, hlam, p2698_1]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2006, hlam, p2698_0]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2517, hlam, p2698_1]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2517, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p2698_1]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h0, h2655, h2696, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2698_1, u4ehi4]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [hlam, p2698_0]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h0, h2694, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2698_1]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h0, h2517, h2655, h2696, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2698_1, u4ehi4]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h0, h2655, h2696, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2698_1, u4ehi4]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2655, h2659, h2696, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2698_1, u4ehi4]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2656, hlam, p2698_1]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [hlam, p2698_0]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2659, hlam, p2698_1]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2655, h2659, h2696, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2698_1, u4ehi4]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2655, h2696, hc04, hlam, hphi, ht0b, ht45, ht5b, p2698_1, u4ehi4]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2657, hlam, p2698_0]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2659, hc03, hc34, hlam, hphi, p2698_1]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [hlam, p2698_0]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2655, h2659, h2696, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2698_1, u4ehi4]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2655, hlam, p2698_0]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2658, hlam, p2698_1]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2694, hlam, p2698_0]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [h2695, hlam, p2698_1]
                  · have p2698_0 := h2698c.1
                    have p2698_1 := h2698c.2.1
                    have p2698_2 := h2698c.2.2.1
                    have p2698_3 := h2698c.2.2.2
                    linarith only [hlam, p2698_0]
                · linarith only [h0, h2655, h2659, h2696, h2697, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
              · linarith only [h2517, h2655, h2695, h2696, hlam]
            · linarith only [h2006, h2655, h2659, h2695, hlam]
          · linarith only [h2006, h2655, h2694, hlam]
      · linarith only [h0, h2655, h2658, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2729 | h2729
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2730 | h2730
        · linarith only [h2656, h2657, h2730, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2732 | h2732
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2733 | h2733
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2734 | h2734
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2735 | h2735
                · rcases h0bigk with h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [hlam, p2736_0]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h0, hlam, p2736_1]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2006, hlam, p2736_0]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2517, hlam, p2736_1]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2655, h2734, hc01, hlam, hphi, ht0b, ht45, ht5b, p2736_1, u4ehi4]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2657, hc01, hc24, hlam, hphi, ht12, p2736_1]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [hlam, p2736_0]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2657, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2736_1]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2657, hlam, p2736_1]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2655, h2657, h2734, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2736_1, u4ehi4]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2655, h2730, h2734, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2736_1, u4ehi4]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2656, hlam, p2736_1]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [hlam, p2736_0]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2730, hlam, p2736_1]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2655, h2730, h2734, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2736_1, u4ehi4]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2655, h2730, h2734, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2736_1, u4ehi4]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2730, hc02, hc34, hlam, hphi, ht23, p2736_1]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2730, hc03, hc34, hlam, hphi, p2736_1]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [hlam, p2736_0]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2655, h2730, h2734, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2736_1, u4ehi4]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2655, hlam, p2736_0]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2729, hlam, p2736_1]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2732, hlam, p2736_0]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [h2733, hlam, p2736_1]
                  · have p2736_0 := h2736c.1
                    have p2736_1 := h2736c.2.1
                    have p2736_2 := h2736c.2.2.1
                    have p2736_3 := h2736c.2.2.2
                    linarith only [hlam, p2736_0]
                · linarith only [h0, h2655, h2730, h2734, h2735, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
              · linarith only [h2517, h2655, h2733, h2734, hc04, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h2655, h2657, h2733, hlam]
          · linarith only [h2006, h2655, h2732, hlam]
      · linarith only [h2006, h2655, h2656, h2729, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2767 | h2767
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2768 | h2768
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2769 | h2769
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2770 | h2770
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2771 | h2771
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2772 | h2772
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2773 | h2773
                · rcases h0bigk with h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [hlam, p2774_0]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h0, hlam, p2774_1]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2006, hlam, p2774_0]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2517, hlam, p2774_1]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2517, h2656, h2767, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2774_1]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2656, hc01, hc23, hlam, hphi, ht12, p2774_1]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [hlam, p2774_0]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2656, hlam, p2774_0]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2656, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2774_1, u4ehi0]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2655, h2656, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2774_1]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2655, hc03, hc15, hlam, hphi, ht0b, ht5b, p2774_1]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2656, hc02, hc23, hlam, hphi, p2774_1]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [hlam, p2774_0]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2656, h2767, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2774_1, u4ehi2]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2656, h2771, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2774_1, u4ehi4]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2655, h2767, h2771, hc02, hlam, hphi, ht0b, ht45, ht5b, p2774_1, u4ehi4]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2767, hlam, p2774_0]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2769, hlam, p2774_0]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [hlam, p2774_0]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2656, h2767, h2771, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2774_1, u4ehi4]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2655, hlam, p2774_0]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2768, hlam, p2774_1]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2770, hlam, p2774_0]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [h2771, hlam, p2774_1]
                  · have p2774_0 := h2774c.1
                    have p2774_1 := h2774c.2.1
                    have p2774_2 := h2774c.2.2.1
                    have p2774_3 := h2774c.2.2.2
                    linarith only [hlam, p2774_0]
                · linarith only [h0, h2655, h2772, h2773, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h2517, h2655, h2771, h2772, hlam]
            · linarith only [h2517, h2655, h2771, hlam]
          · linarith only [h0, h2655, h2656, h2770, hlam]
        · linarith only [h2656, h2767, h2769, hlam]
      · linarith only [h2517, h2655, h2767, h2768, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2806 | h2806
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2807 | h2807
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2808 | h2808
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2809 | h2809
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2810 | h2810
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2811 | h2811
                · rcases h0bigk with h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [hlam, p2812_0]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h0, hlam, p2812_1]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2006, hlam, p2812_0]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2517, hlam, p2812_1]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h0, h2767, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p2812_1]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2655, h2767, hc04, hc15, hlam, hphi, ht0b, ht5b, p2812_1]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [hlam, p2812_0]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2656, hlam, p2812_0]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2767, hlam, p2812_1]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2767, h2808, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2812_1]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2655, h2656, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2812_1]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2656, hc02, hc23, hlam, hphi, p2812_1]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [hlam, p2812_0]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2656, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2812_1, u4ehi0]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2656, h2809, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2812_1, u4ehi4]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2655, h2809, hc04, hlam, hphi, ht0b, ht45, ht5b, p2812_1, u4ehi4]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h0, h2655, h2767, h2809, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2812_1, u4ehi4]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2807, hlam, p2812_0]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [hlam, p2812_0]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2656, h2807, h2809, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2812_1, u4ehi4]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2655, hlam, p2812_0]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2806, hlam, p2812_1]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2808, hlam, p2812_0]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [h2809, hlam, p2812_1]
                  · have p2812_0 := h2812c.1
                    have p2812_1 := h2812c.2.1
                    have p2812_2 := h2812c.2.2.1
                    have p2812_3 := h2812c.2.2.2
                    linarith only [hlam, p2812_0]
                · linarith only [h0, h2655, h2810, h2811, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h2517, h2809, h2810, hlam]
            · linarith only [h0, h2655, h2767, h2809, hlam]
          · linarith only [h2006, h2655, h2808, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2842 | h2842
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2843 | h2843
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2844 | h2844
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2845 | h2845
                · rcases h0bigk with h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [hlam, p2846_0]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h0, hlam, p2846_1]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2006, hlam, p2846_0]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2517, hlam, p2846_1]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h0, h2656, h2807, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2846_1]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2655, h2656, h2807, hc04, hc15, hlam, hphi, ht0b, ht5b, p2846_1]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [hlam, p2846_0]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2656, hlam, p2846_0]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2767, hlam, p2846_1]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2655, h2656, h2807, h2844, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2846_1, u4ehi4]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2655, h2807, h2844, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2846_1, u4ehi4]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2807, hc02, hc34, hlam, hphi, ht23, p2846_1]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [hlam, p2846_0]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2807, hlam, p2846_1]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2655, h2807, h2844, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2846_1, u4ehi4]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2655, h2807, h2844, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2846_1, u4ehi4]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h0, h2655, h2807, h2844, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2846_1, u4ehi4]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2807, hc03, hc34, hlam, hphi, p2846_1]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [hlam, p2846_0]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2655, h2807, h2844, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2846_1, u4ehi4]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2655, hlam, p2846_0]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2806, hlam, p2846_1]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2842, hlam, p2846_0]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [h2843, hlam, p2846_1]
                  · have p2846_0 := h2846c.1
                    have p2846_1 := h2846c.2.1
                    have p2846_2 := h2846c.2.2.1
                    have p2846_3 := h2846c.2.2.2
                    linarith only [hlam, p2846_0]
                · linarith only [h0, h2655, h2807, h2844, h2845, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
              · linarith only [h0, h2517, h2655, h2656, h2807, h2843, h2844, hlam]
            · linarith only [h0, h2655, h2656, h2807, h2843, hlam]
          · linarith only [h0, h2655, h2656, h2842, hlam]
      · linarith only [h0, h2655, h2806, hlam]

end R2N4
