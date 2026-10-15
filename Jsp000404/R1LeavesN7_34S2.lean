import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_34S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h2084 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2085 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2086 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2087 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h2088 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h2089 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 2 3 5 (by decide) (by decide) with h2658 | h2658
  · rcases m.htr 2 4 5 (by decide) (by decide) with h2659 | h2659
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2660 | h2660
      · rcases h0bigk with h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [hlam, p2661_0]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h0, hlam, p2661_1]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h1265, hlam, p2661_0]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h1561, h2083, hlam, p2661_1]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h1561, hlam, p2661_1]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          rcases p2661_3 (m.d 0 1) (by simp) with h2667 | h2667
          · linarith only [h0, h2667, hlam]
          · rcases p2661_3 (m.d 0 2) (by simp) with h2669 | h2669
            · rcases p2661_3 (m.d 0 3) (by simp) with h2670 | h2670
              · linarith only [h2078, h2670, hlam]
              · linarith only [h1265, h2670, hlam]
            · linarith only [h0, h2669, hlam]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [hlam, p2661_0]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h0, h2081, h2089, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2661_1]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h0, h2081, h2089, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2661_1, u2ehi4]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          rcases p2661_3 (m.d 0 1) (by simp) with h2677 | h2677
          · linarith only [h0, h2677, hlam]
          · rcases p2661_3 (m.d 0 2) (by simp) with h2679 | h2679
            · rcases p2661_3 (m.d 0 3) (by simp) with h2680 | h2680
              · linarith only [h2078, h2680, hlam]
              · linarith only [h2082, h2680, hlam]
            · linarith only [h2080, h2679, hlam]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          rcases p2661_3 (m.d 0 1) (by simp) with h2684 | h2684
          · linarith only [h1265, h2684, hlam]
          · rcases p2661_3 (m.d 0 2) (by simp) with h2686 | h2686
            · rcases p2661_3 (m.d 0 3) (by simp) with h2687 | h2687
              · rcases p2661_3 (m.d 0 4) (by simp) with h2688 | h2688
                · linarith only [h2081, h2688, hlam]
                · linarith only [h2081, h2089, h2658, h2688, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2661_1, u2ehi4]
              · linarith only [h1265, h2687, hlam]
            · linarith only [h0, h2686, hlam]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h2078, hlam, p2661_1]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [hlam, p2661_0]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h1265, h2081, h2084, h2089, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2661_1, u2ehi4]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          rcases p2661_3 (m.d 0 1) (by simp) with h2696 | h2696
          · linarith only [h1265, h2696, hlam]
          · rcases p2661_3 (m.d 0 2) (by simp) with h2698 | h2698
            · rcases p2661_3 (m.d 0 3) (by simp) with h2699 | h2699
              · rcases p2661_3 (m.d 0 4) (by simp) with h2700 | h2700
                · linarith only [h2081, h2700, hlam]
                · linarith only [h2083, h2700, hlam]
              · linarith only [h2082, h2699, hlam]
            · linarith only [h2080, h2698, hlam]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          rcases p2661_3 (m.d 0 1) (by simp) with h2705 | h2705
          · linarith only [h2705, hlam, p2661_0]
          · rcases p2661_3 (m.d 0 2) (by simp) with h2707 | h2707
            · rcases p2661_3 (m.d 0 3) (by simp) with h2708 | h2708
              · rcases p2661_3 (m.d 0 4) (by simp) with h2709 | h2709
                · rcases p2661_3 (m.d 0 5) (by simp) with h2710 | h2710
                  · linarith only [h2083, h2710, hlam]
                  · linarith only [h1561, h2710, hlam]
                · linarith only [h2709, hlam, p2661_0]
              · linarith only [h1265, h2708, hlam]
            · linarith only [h0, h2707, hlam]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h2079, hlam, p2661_0]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h2081, hlam, p2661_0]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [hlam, p2661_0]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          rcases p2661_3 (m.d 0 1) (by simp) with h2719 | h2719
          · linarith only [h1561, h2719, hlam, p2661_1]
          · rcases p2661_3 (m.d 0 2) (by simp) with h2721 | h2721
            · rcases p2661_3 (m.d 0 3) (by simp) with h2722 | h2722
              · rcases p2661_3 (m.d 0 4) (by simp) with h2723 | h2723
                · rcases p2661_3 (m.d 0 5) (by simp) with h2724 | h2724
                  · linarith only [h2083, h2724, hlam]
                  · rcases h3bigk with h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h1265, hlam, p2726_1]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h1265, h2084, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2726_1, u2ehi4]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h1265, h2084, h2089, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2726_1, u2ehi4]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      rcases p2726_3 (m.d 0 3) (by simp) with h2731 | h2731
                      · rcases p2726_3 (m.d 1 3) (by simp) with h2732 | h2732
                        · rcases p2726_3 (m.d 2 3) (by simp) with h2733 | h2733
                          · linarith only [h2078, h2733, hlam]
                          · linarith only [h2658, h2733, hlam]
                        · linarith only [h2087, h2732, hlam]
                      · linarith only [h2731, hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h1561, h2081, h2084, hc01, hc12, hlam, hphi, p2661_1, p2726_1]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h2084, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2726_1, u2ehi4]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h2084, h2089, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2726_1, u2ehi4]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      rcases p2726_3 (m.d 0 3) (by simp) with h2742 | h2742
                      · linarith only [h1265, h2742, hlam]
                      · linarith only [h2082, h2742, hlam]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h2078, hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h2084, hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h2089, hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h2089, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2726_1]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h2081, hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h2086, hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [hc23, hc34, hlam, hphi, p2726_1]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h1265, h2081, h2084, h2660, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2726_1]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h2082, hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h2087, hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h2658, hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [h2660, hlam, p2726_0]
                    · have p2726_0 := h2726c.1
                      have p2726_1 := h2726c.2.1
                      have p2726_2 := h2726c.2.2.1
                      have p2726_3 := h2726c.2.2.2
                      linarith only [hlam, p2726_0]
                · linarith only [h2083, h2723, hlam]
              · linarith only [h2082, h2722, hlam]
            · linarith only [h2080, h2721, hlam]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          rcases p2661_3 (m.d 0 1) (by simp) with h2763 | h2763
          · linarith only [h1561, h2763, hlam]
          · rcases p2661_3 (m.d 0 2) (by simp) with h2765 | h2765
            · rcases p2661_3 (m.d 0 3) (by simp) with h2766 | h2766
              · rcases p2661_3 (m.d 0 4) (by simp) with h2767 | h2767
                · rcases p2661_3 (m.d 0 5) (by simp) with h2768 | h2768
                  · rcases h3bigk with h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c | h2769c
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h1265, hlam, p2769_1]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h1265, h2084, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2769_1, u2ehi4]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h1265, h2084, h2089, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2769_1, u2ehi3]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      rcases p2769_3 (m.d 0 3) (by simp) with h2774 | h2774
                      · rcases p2769_3 (m.d 1 3) (by simp) with h2775 | h2775
                        · rcases p2769_3 (m.d 2 3) (by simp) with h2776 | h2776
                          · linarith only [h2078, h2776, hlam]
                          · linarith only [h2658, h2776, hlam]
                        · linarith only [h2087, h2775, hlam]
                      · linarith only [h2774, hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h1265, h2084, hc01, hc12, hlam, hphi, p2769_1]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2084, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2769_1, u2ehi4]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2084, h2089, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2769_1, u2ehi4]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      rcases p2769_3 (m.d 0 3) (by simp) with h2785 | h2785
                      · linarith only [h1265, h2785, hlam]
                      · linarith only [h2082, h2785, hlam]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2078, hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2084, hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2089, hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2081, h2089, h2660, hc03, hc45, hlam, hphi, ht0b, ht5b, p2769_1]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2081, hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2086, hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2081, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2769_1]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h1265, h2081, h2084, h2660, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2769_1]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2082, hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2087, hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2658, hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [h2660, hlam, p2769_0]
                    · have p2769_0 := h2769c.1
                      have p2769_1 := h2769c.2.1
                      have p2769_2 := h2769c.2.2.1
                      have p2769_3 := h2769c.2.2.2
                      linarith only [hlam, p2769_0]
                  · linarith only [h1561, h2768, hlam]
                · linarith only [h2083, h2767, hlam, p2661_1]
              · linarith only [h1265, h2766, hlam]
            · linarith only [h0, h2765, hlam]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h2080, hlam, p2661_1]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h2082, hlam, p2661_0]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [h2083, hlam, p2661_1]
        · have p2661_0 := h2661c.1
          have p2661_1 := h2661c.2.1
          have p2661_2 := h2661c.2.2.1
          have p2661_3 := h2661c.2.2.2
          linarith only [hlam, p2661_0]
      · linarith only [h1265, h2081, h2083, h2084, h2089, h2658, h2660, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
    · linarith only [h2089, h2658, h2659, hlam]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h2813 | h2813
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2814 | h2814
      · rcases h0bigk with h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c | h2815c
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [hlam, p2815_0]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h0, hlam, p2815_1]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h1265, hlam, p2815_0]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h1561, h2079, h2086, h2088, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2815_1, u2ehi3]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h1561, hlam, p2815_1]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          rcases p2815_3 (m.d 0 1) (by simp) with h2821 | h2821
          · linarith only [h0, h2821, hlam]
          · rcases p2815_3 (m.d 0 2) (by simp) with h2823 | h2823
            · rcases p2815_3 (m.d 0 3) (by simp) with h2824 | h2824
              · linarith only [h2078, h2824, hlam]
              · linarith only [h1265, h2824, hlam]
            · linarith only [h0, h2823, hlam]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [hlam, p2815_0]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h0, h2081, h2658, h2814, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2815_1, u2ehi2]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h0, h2081, h2658, h2814, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2815_1, u2ehi2]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h0, h2082, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2815_1, u2ehi2]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          rcases p2815_3 (m.d 0 1) (by simp) with h2832 | h2832
          · linarith only [h1265, h2832, hlam]
          · rcases p2815_3 (m.d 0 2) (by simp) with h2834 | h2834
            · rcases p2815_3 (m.d 0 3) (by simp) with h2835 | h2835
              · rcases p2815_3 (m.d 0 4) (by simp) with h2836 | h2836
                · linarith only [h2081, h2836, hlam]
                · linarith only [h2081, h2658, h2814, h2836, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2815_1, u2ehi2]
              · linarith only [h1265, h2835, hlam]
            · linarith only [h0, h2834, hlam]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h2078, hlam, p2815_1]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [hlam, p2815_0]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h1265, h2081, h2084, h2658, h2814, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2815_1, u2ehi2]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h1265, h2082, h2084, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2815_1, u2ehi2]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          rcases p2815_3 (m.d 0 1) (by simp) with h2845 | h2845
          · linarith only [h2845, hlam, p2815_0]
          · rcases p2815_3 (m.d 0 2) (by simp) with h2847 | h2847
            · rcases p2815_3 (m.d 0 3) (by simp) with h2848 | h2848
              · rcases p2815_3 (m.d 0 4) (by simp) with h2849 | h2849
                · rcases p2815_3 (m.d 0 5) (by simp) with h2850 | h2850
                  · linarith only [h2083, h2850, hlam]
                  · linarith only [h1561, h2850, hlam]
                · linarith only [h2849, hlam, p2815_0]
              · linarith only [h1265, h2848, hlam]
            · linarith only [h0, h2847, hlam]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h2079, hlam, p2815_0]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h2081, hlam, p2815_0]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [hlam, p2815_0]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h2082, h2658, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2815_1, u2ehi2]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          rcases p2815_3 (m.d 0 1) (by simp) with h2860 | h2860
          · linarith only [h1561, h2860, hlam]
          · rcases p2815_3 (m.d 0 2) (by simp) with h2862 | h2862
            · rcases p2815_3 (m.d 0 3) (by simp) with h2863 | h2863
              · rcases p2815_3 (m.d 0 4) (by simp) with h2864 | h2864
                · rcases p2815_3 (m.d 0 5) (by simp) with h2865 | h2865
                  · rcases h3bigk with h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h1265, hlam, p2866_1]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h1265, h2084, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2866_1, u2ehi2]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h1265, h2084, h2658, h2814, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2866_1, u2ehi2]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h1265, h2084, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2866_1, u2ehi2]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h1265, h2084, hc01, hc12, hlam, hphi, p2866_1]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2084, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2866_1, u2ehi2]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2084, h2658, h2814, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2866_1, u2ehi2]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2084, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2866_1, u2ehi2]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2078, hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2084, hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2089, hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2658, hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2081, hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2086, hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2081, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2866_1, u2ehi2]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h1265, h2081, h2084, h2658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2866_1, u2ehi2]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2082, hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2087, hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [hc35, hlam, hphi, ht23, p2866_1, u2ehi2]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [h2814, hlam, p2866_0]
                    · have p2866_0 := h2866c.1
                      have p2866_1 := h2866c.2.1
                      have p2866_2 := h2866c.2.2.1
                      have p2866_3 := h2866c.2.2.2
                      linarith only [hlam, p2866_0]
                  · linarith only [h1561, h2865, hlam]
                · linarith only [h2083, h2864, hlam, p2815_1]
              · linarith only [h1265, h2863, hlam]
            · linarith only [h0, h2862, hlam]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h2080, hlam, p2815_1]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h2082, hlam, p2815_0]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [h2083, hlam, p2815_1]
        · have p2815_0 := h2815c.1
          have p2815_1 := h2815c.2.1
          have p2815_2 := h2815c.2.2.1
          have p2815_3 := h2815c.2.2.2
          linarith only [hlam, p2815_0]
      · linarith only [h2089, h2814, hc45, hlam, hphi, ht23, ht34, u2ehi2]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2901 | h2901
      · linarith only [h2813, h2901, hc34, hlam, hphi, ht23, u2ehi3]
      · linarith only [h1265, h2081, h2083, h2084, h2089, h2901, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h2084 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2085 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2086 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2087 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h2088 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 2 3 4 (by decide) (by decide) with h2089 | h2089
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083 h2084 h2085 h2086 h2087 h2088 h2089
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083 h2084 h2085 h2086 h2087 h2088 h2089

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h2084 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2085 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2086 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2087 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h2088 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  linarith only [h1561, h2083, h2088, hlam]

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h2084 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2085 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2086 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2087 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 1 4 5 (by decide) (by decide) with h2088 | h2088
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083 h2084 h2085 h2086 h2087 h2088
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083 h2084 h2085 h2086 h2087 h2088

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h2084 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2085 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2086 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2087 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  linarith only [h1265, h2082, h2087, hlam]

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h2084 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2085 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2086 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 1 3 5 (by decide) (by decide) with h2087 | h2087
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083 h2084 h2085 h2086 h2087
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083 h2084 h2085 h2086 h2087

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h2084 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2085 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2086 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  linarith only [h1265, h2081, h2086, hlam]

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h2084 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2085 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 1 3 4 (by decide) (by decide) with h2086 | h2086
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083 h2084 h2085 h2086
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083 h2084 h2085 h2086

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h2084 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2085 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  linarith only [h0, h2078, h2085, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h2084 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 1 2 4 (by decide) (by decide) with h2085 | h2085
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083 h2084 h2085
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083 h2084 h2085

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h2084 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  linarith only [h0, h2079, h2084, hc23, hlam, hphi, u2ehi3]

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 1 2 3 (by decide) (by decide) with h2084 | h2084
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083 h2084
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081 h2082 h2083 h2084

end R2N4
