import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_28S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1972 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1973 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1974 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1975 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1976 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1977 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 2 3 5 (by decide) (by decide) with h2657 | h2657
  · rcases m.htr 2 4 5 (by decide) (by decide) with h2658 | h2658
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2659 | h2659
      · rcases h0bigk with h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c | h2660c
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [hlam, p2660_0]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h0, hlam, p2660_1]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h1414, hlam, p2660_0]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h1728, h1966, h1971, h1974, h1976, h1977, h2657, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2660_1, u2ehi4]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h1728, hlam, p2660_1]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          rcases p2660_3 (m.d 0 1) (by simp) with h2666 | h2666
          · linarith only [h0, h2666, hlam]
          · rcases p2660_3 (m.d 0 2) (by simp) with h2668 | h2668
            · rcases p2660_3 (m.d 0 3) (by simp) with h2669 | h2669
              · linarith only [h1965, h2669, hlam]
              · linarith only [h1414, h2669, hlam]
            · linarith only [h0, h2668, hlam]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [hlam, p2660_0]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h0, h1968, h1977, h2657, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2660_1, u2ehi4]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h0, h1968, h1977, h2657, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2660_1, u2ehi4]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          rcases p2660_3 (m.d 0 1) (by simp) with h2676 | h2676
          · linarith only [h0, h2676, hlam]
          · rcases p2660_3 (m.d 0 2) (by simp) with h2678 | h2678
            · rcases p2660_3 (m.d 0 3) (by simp) with h2679 | h2679
              · linarith only [h1965, h2679, hlam]
              · linarith only [h1969, h2679, hlam]
            · linarith only [h1967, h2678, hlam]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          rcases p2660_3 (m.d 0 1) (by simp) with h2683 | h2683
          · linarith only [h1414, h2683, hlam]
          · rcases p2660_3 (m.d 0 2) (by simp) with h2685 | h2685
            · rcases p2660_3 (m.d 0 3) (by simp) with h2686 | h2686
              · rcases p2660_3 (m.d 0 4) (by simp) with h2687 | h2687
                · linarith only [h1968, h2687, hlam]
                · linarith only [h1968, h1977, h2657, h2687, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2660_1, u2ehi4]
              · linarith only [h1414, h2686, hlam]
            · linarith only [h0, h2685, hlam]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h1965, hlam, p2660_1]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [hlam, p2660_0]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h0, h1965, h1968, h1977, h2657, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2660_1, u2ehi4]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          rcases p2660_3 (m.d 0 1) (by simp) with h2695 | h2695
          · linarith only [h1414, h2695, hlam]
          · rcases p2660_3 (m.d 0 2) (by simp) with h2697 | h2697
            · rcases p2660_3 (m.d 0 3) (by simp) with h2698 | h2698
              · rcases p2660_3 (m.d 0 4) (by simp) with h2699 | h2699
                · linarith only [h1968, h2699, hlam]
                · linarith only [h1970, h2699, hlam]
              · linarith only [h1969, h2698, hlam]
            · linarith only [h1967, h2697, hlam]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          rcases p2660_3 (m.d 0 1) (by simp) with h2704 | h2704
          · linarith only [h2704, hlam, p2660_0]
          · rcases p2660_3 (m.d 0 2) (by simp) with h2706 | h2706
            · rcases p2660_3 (m.d 0 3) (by simp) with h2707 | h2707
              · rcases p2660_3 (m.d 0 4) (by simp) with h2708 | h2708
                · rcases p2660_3 (m.d 0 5) (by simp) with h2709 | h2709
                  · linarith only [h1970, h2709, hlam]
                  · linarith only [h1728, h2709, hlam]
                · linarith only [h2708, hlam, p2660_0]
              · linarith only [h1414, h2707, hlam]
            · linarith only [h0, h2706, hlam]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h1966, hlam, p2660_0]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h1968, hlam, p2660_0]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [hlam, p2660_0]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          rcases p2660_3 (m.d 0 1) (by simp) with h2718 | h2718
          · linarith only [h1728, h2718, hlam, p2660_1]
          · rcases p2660_3 (m.d 0 2) (by simp) with h2720 | h2720
            · rcases p2660_3 (m.d 0 3) (by simp) with h2721 | h2721
              · rcases p2660_3 (m.d 0 4) (by simp) with h2722 | h2722
                · rcases p2660_3 (m.d 0 5) (by simp) with h2723 | h2723
                  · linarith only [h1970, h2723, hlam]
                  · rcases h0emax with h2725 | h2725 | h2725 | h2725 | h2725
                    · rcases h5bigk with h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [hlam, p2726_0]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h1728, hlam, p2726_1]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2660_1, p2726_1, u2ehi4]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2660_1, p2726_1]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2660_1, p2726_1]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h1728, h1976, hc01, hc14, hlam, hphi, p2726_1]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [hlam, p2726_0]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h1972, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2726_1, u2ehi4]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        rcases p2726_3 (m.d 0 5) (by simp) with h2735 | h2735
                        · linarith only [h1728, h2735, hlam]
                        · linarith only [h1969, h2735, hlam]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        rcases p2726_3 (m.d 0 5) (by simp) with h2738 | h2738
                        · linarith only [h1728, h2738, hlam]
                        · linarith only [h1970, h2738, hlam]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h1967, hlam, p2726_1]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h1973, hlam, p2726_1]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [hlam, p2726_0]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h1977, h2657, h2659, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2726_1]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h0, h1965, h1967, h1968, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2660_1, p2726_1]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h1969, hlam, p2726_0]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h1975, hlam, p2726_0]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h2657, hlam, p2726_0]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [hlam, p2726_0]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h0, h1965, h1969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2726_1]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h1970, hlam, p2726_0]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h1976, hlam, p2726_0]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h2658, hlam, p2726_0]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [h2659, hlam, p2726_0]
                      · have p2726_0 := h2726c.1
                        have p2726_1 := h2726c.2.1
                        have p2726_2 := h2726c.2.2.1
                        have p2726_3 := h2726c.2.2.2
                        linarith only [hlam, p2726_0]
                    · linarith only [h1965, h1968, h2725, hc05, hlam, hphi, ht0b, ht5b, p2660_1]
                    · linarith only [h1967, h1968, h2725, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2660_1, u2ehi4]
                    · linarith only [h1967, h2725, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2660_1, u2ehi4]
                    · rcases h5bigk with h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [hlam, p2759_0]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h1728, hlam, p2759_1]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h1965, h1968, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2660_1, p2759_1, u2ehi4]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2660_1, p2759_1]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2660_1, p2759_1]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h1728, h1971, h1974, h1976, hc01, hc12, hlam, hphi, p2759_1]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [hlam, p2759_0]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h1971, h1974, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2759_1, u2ehi4]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        rcases p2759_3 (m.d 0 5) (by simp) with h2768 | h2768
                        · linarith only [h1728, h2768, hlam]
                        · linarith only [h1969, h2768, hlam]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        rcases p2759_3 (m.d 0 5) (by simp) with h2771 | h2771
                        · linarith only [h1728, h2771, hlam]
                        · linarith only [h1970, h2771, hlam]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h1967, hlam, p2759_1]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h1973, hlam, p2759_1]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [hlam, p2759_0]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h0, h1967, h2659, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2759_1]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h0, h1965, h1967, h1968, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2660_1, p2759_1]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h1969, hlam, p2759_0]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h1975, hlam, p2759_0]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h2657, hlam, p2759_0]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [hlam, p2759_0]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h0, h1965, h1969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2759_1]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h1970, hlam, p2759_0]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h1976, hlam, p2759_0]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h2658, hlam, p2759_0]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [h2659, hlam, p2759_0]
                      · have p2759_0 := h2759c.1
                        have p2759_1 := h2759c.2.1
                        have p2759_2 := h2759c.2.2.1
                        have p2759_3 := h2759c.2.2.2
                        linarith only [hlam, p2759_0]
                · linarith only [h1970, h2722, hlam]
              · linarith only [h1969, h2721, hlam]
            · linarith only [h1967, h2720, hlam]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          rcases p2660_3 (m.d 0 1) (by simp) with h2792 | h2792
          · linarith only [h1728, h2792, hlam]
          · rcases p2660_3 (m.d 0 2) (by simp) with h2794 | h2794
            · rcases p2660_3 (m.d 0 3) (by simp) with h2795 | h2795
              · rcases p2660_3 (m.d 0 4) (by simp) with h2796 | h2796
                · rcases p2660_3 (m.d 0 5) (by simp) with h2797 | h2797
                  · rcases h0emax with h2798 | h2798 | h2798 | h2798 | h2798
                    · rcases h5bigk with h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c | h2799c
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [hlam, p2799_0]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h1728, hlam, p2799_1]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2799_1, u2ehi4]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        rcases p2799_3 (m.d 0 5) (by simp) with h2803 | h2803
                        · rcases p2799_3 (m.d 1 5) (by simp) with h2804 | h2804
                          · rcases p2799_3 (m.d 2 5) (by simp) with h2805 | h2805
                            · linarith only [h1967, h2805, hlam]
                            · linarith only [h2657, h2805, hlam]
                          · linarith only [h1975, h2804, hlam]
                        · linarith only [h1969, h2803, hlam]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        rcases p2799_3 (m.d 0 5) (by simp) with h2810 | h2810
                        · rcases p2799_3 (m.d 1 5) (by simp) with h2811 | h2811
                          · rcases p2799_3 (m.d 2 5) (by simp) with h2812 | h2812
                            · linarith only [h1967, h2812, hlam]
                            · linarith only [h2658, h2812, hlam]
                          · linarith only [h1976, h2811, hlam]
                        · linarith only [h1970, h2810, hlam]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h1971, h1974, h1976, hc01, hc12, hlam, hphi, p2660_1, p2799_1]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [hlam, p2799_0]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h1971, h1974, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2799_1, u2ehi4]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        rcases p2799_3 (m.d 0 5) (by simp) with h2820 | h2820
                        · linarith only [h1728, h2820, hlam]
                        · linarith only [h1969, h2820, hlam]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        rcases p2799_3 (m.d 0 5) (by simp) with h2823 | h2823
                        · linarith only [h1728, h2823, hlam]
                        · linarith only [h1970, h2823, hlam]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h1967, hlam, p2799_1]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h1973, hlam, p2799_1]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [hlam, p2799_0]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h0, h1967, h2659, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2799_1]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h0, h1965, h1968, h1977, h2657, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2799_1]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h1969, hlam, p2799_0]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h1975, hlam, p2799_0]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h2657, hlam, p2799_0]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [hlam, p2799_0]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h0, h1965, h1969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2799_1]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h1970, hlam, p2799_0]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h1976, hlam, p2799_0]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h2658, hlam, p2799_0]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [h2659, hlam, p2799_0]
                      · have p2799_0 := h2799c.1
                        have p2799_1 := h2799c.2.1
                        have p2799_2 := h2799c.2.2.1
                        have p2799_3 := h2799c.2.2.2
                        linarith only [hlam, p2799_0]
                    · linarith only [h1965, h1968, h1977, h2798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1968, h1977, h2657, h2798, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h1968, h1977, h2657, h2798, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h2798, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2660_1]
                  · linarith only [h1728, h2797, hlam]
                · linarith only [h1970, h2796, hlam, p2660_1]
              · linarith only [h1414, h2795, hlam]
            · linarith only [h0, h2794, hlam]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h1967, hlam, p2660_1]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h1969, hlam, p2660_0]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [h1970, hlam, p2660_1]
        · have p2660_0 := h2660c.1
          have p2660_1 := h2660c.2.1
          have p2660_2 := h2660c.2.2.1
          have p2660_3 := h2660c.2.2.2
          linarith only [hlam, p2660_0]
      · linarith only [h1977, h2657, h2659, hc45, hlam, hphi, ht23, ht34, u2ehi4]
    · linarith only [h1977, h2657, h2658, hlam]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h2855 | h2855
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2856 | h2856
      · rcases h0bigk with h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c | h2857c
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [hlam, p2857_0]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h0, hlam, p2857_1]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h1414, hlam, p2857_0]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h0, h1966, h2855, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2857_1]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h1728, hlam, p2857_1]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          rcases p2857_3 (m.d 0 1) (by simp) with h2863 | h2863
          · linarith only [h0, h2863, hlam]
          · rcases p2857_3 (m.d 0 2) (by simp) with h2865 | h2865
            · rcases p2857_3 (m.d 0 3) (by simp) with h2866 | h2866
              · linarith only [h1965, h2866, hlam]
              · linarith only [h1414, h2866, hlam]
            · linarith only [h0, h2865, hlam]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [hlam, p2857_0]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h0, h1968, h2657, h2856, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2857_1, u2ehi2]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h0, h1968, h2657, h2856, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2857_1, u2ehi2]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h0, h1969, h2657, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2857_1, u2ehi2]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          rcases p2857_3 (m.d 0 1) (by simp) with h2874 | h2874
          · linarith only [h1414, h2874, hlam]
          · rcases p2857_3 (m.d 0 2) (by simp) with h2876 | h2876
            · rcases p2857_3 (m.d 0 3) (by simp) with h2877 | h2877
              · rcases p2857_3 (m.d 0 4) (by simp) with h2878 | h2878
                · linarith only [h1968, h2878, hlam]
                · linarith only [h1968, h2657, h2856, h2878, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2857_1, u2ehi2]
              · linarith only [h1414, h2877, hlam]
            · linarith only [h0, h2876, hlam]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h1965, hlam, p2857_1]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [hlam, p2857_0]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h1414, h1968, h1971, h2657, h2856, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2857_1, u2ehi2]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h1414, h1969, h1971, h2657, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2857_1, u2ehi2]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          rcases p2857_3 (m.d 0 1) (by simp) with h2887 | h2887
          · linarith only [h2887, hlam, p2857_0]
          · rcases p2857_3 (m.d 0 2) (by simp) with h2889 | h2889
            · rcases p2857_3 (m.d 0 3) (by simp) with h2890 | h2890
              · rcases p2857_3 (m.d 0 4) (by simp) with h2891 | h2891
                · rcases p2857_3 (m.d 0 5) (by simp) with h2892 | h2892
                  · linarith only [h1970, h2892, hlam]
                  · linarith only [h1728, h2892, hlam]
                · linarith only [h2891, hlam, p2857_0]
              · linarith only [h1414, h2890, hlam]
            · linarith only [h0, h2889, hlam]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h1966, hlam, p2857_0]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h1968, hlam, p2857_0]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [hlam, p2857_0]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h1969, h2657, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2857_1, u2ehi2]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          rcases p2857_3 (m.d 0 1) (by simp) with h2902 | h2902
          · linarith only [h1728, h2902, hlam]
          · rcases p2857_3 (m.d 0 2) (by simp) with h2904 | h2904
            · rcases p2857_3 (m.d 0 3) (by simp) with h2905 | h2905
              · rcases p2857_3 (m.d 0 4) (by simp) with h2906 | h2906
                · rcases p2857_3 (m.d 0 5) (by simp) with h2907 | h2907
                  · rcases h0emax with h2908 | h2908 | h2908 | h2908 | h2908
                    · rcases h5bigk with h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c | h2909c
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [hlam, p2909_0]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h1728, hlam, p2909_1]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h2657, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2909_1, u2ehi2]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h1728, h1971, h1974, h1976, h2657, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2909_1, u2ehi2]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        rcases p2909_3 (m.d 0 5) (by simp) with h2914 | h2914
                        · rcases p2909_3 (m.d 1 5) (by simp) with h2915 | h2915
                          · rcases p2909_3 (m.d 2 5) (by simp) with h2916 | h2916
                            · linarith only [h1967, h2916, hlam]
                            · linarith only [h2855, h2916, hlam]
                          · linarith only [h1976, h2915, hlam]
                        · linarith only [h1970, h2914, hlam]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h1971, h1974, h1976, hc01, hc12, hlam, hphi, p2857_1, p2909_1]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [hlam, p2909_0]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h1971, h1974, h1976, h2657, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2909_1, u2ehi2]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h1971, h1974, h1976, h2657, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2909_1, u2ehi2]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        rcases p2909_3 (m.d 0 5) (by simp) with h2925 | h2925
                        · linarith only [h1728, h2925, hlam]
                        · linarith only [h1970, h2925, hlam]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h1967, hlam, p2909_1]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h1973, hlam, p2909_1]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [hlam, p2909_0]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h2657, hlam, p2909_1]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h0, h1966, h2855, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2909_1]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h1969, hlam, p2909_0]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h1975, hlam, p2909_0]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [hc35, hlam, hphi, ht23, p2909_1, u2ehi4]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [hlam, p2909_0]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h1414, h1968, h1971, h2856, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2909_1]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h1970, hlam, p2909_0]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h1976, hlam, p2909_0]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h2855, hlam, p2909_0]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [h2856, hlam, p2909_0]
                      · have p2909_0 := h2909c.1
                        have p2909_1 := h2909c.2.1
                        have p2909_2 := h2909c.2.2.1
                        have p2909_3 := h2909c.2.2.2
                        linarith only [hlam, p2909_0]
                    · linarith only [h1965, h2908, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h1968, h1977, h2908, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h1970, h2908, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2857_1]
                    · linarith only [h0, h1965, h1968, h2657, h2856, h2908, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2857_1, u2ehi2]
                  · linarith only [h1728, h2907, hlam]
                · linarith only [h1970, h2906, hlam, p2857_1]
              · linarith only [h1414, h2905, hlam]
            · linarith only [h0, h2904, hlam]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h1967, hlam, p2857_1]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h1969, hlam, p2857_0]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [h1970, hlam, p2857_1]
        · have p2857_0 := h2857c.1
          have p2857_1 := h2857c.2.1
          have p2857_2 := h2857c.2.2.1
          have p2857_3 := h2857c.2.2.2
          linarith only [hlam, p2857_0]
      · linarith only [h0, h1965, h1968, h1970, h1977, h2856, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2956 | h2956
      · linarith only [h2855, h2956, hc34, hlam, hphi, ht23, u2ehi3]
      · linarith only [h0, h1965, h1968, h1970, h1977, h2956, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1972 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1973 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1974 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1975 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1976 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 2 3 4 (by decide) (by decide) with h1977 | h1977
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971 h1972 h1973 h1974 h1975 h1976 h1977
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971 h1972 h1973 h1974 h1975 h1976 h1977

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1972 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1973 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1974 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1975 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  linarith only [h1728, h1970, h1976, hlam]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1972 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1973 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1974 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1975 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 1 4 5 (by decide) (by decide) with h1976 | h1976
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971 h1972 h1973 h1974 h1975 h1976
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971 h1972 h1973 h1974 h1975 h1976

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1972 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1973 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1974 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1975 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  linarith only [h1414, h1969, h1975, hlam]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1972 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1973 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1974 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 1 3 5 (by decide) (by decide) with h1975 | h1975
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971 h1972 h1973 h1974 h1975
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971 h1972 h1973 h1974 h1975

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1972 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1973 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1974 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  linarith only [h1414, h1968, h1974, hlam]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1972 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1973 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 1 3 4 (by decide) (by decide) with h1974 | h1974
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971 h1972 h1973 h1974
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971 h1972 h1973 h1974

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1972 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1973 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  linarith only [h0, h1965, h1973, hc25, hlam, hphi, u2ehi2]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1972 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 1 2 5 (by decide) (by decide) with h1973 | h1973
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971 h1972 h1973
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971 h1972 h1973

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1972 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  linarith only [h0, h1965, h1972, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 1 2 4 (by decide) (by decide) with h1972 | h1972
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971 h1972
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971 h1972

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  linarith only [h0, h1966, h1971, hc23, hlam, hphi, u2ehi3]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 1 2 3 (by decide) (by decide) with h1971 | h1971
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969 h1970 h1971

end R2N4
