import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_17S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6988000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s6_x1_x1_x1 (m : N7Model)
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
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h2153 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h2340 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h2703 | h2703
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2704 | h2704
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2705 | h2705
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2706 | h2706
        · linarith only [h1, h2706, h7, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2708 | h2708
          · linarith only [h2, h2340, h2708, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2710 | h2710
            · linarith only [h1, h2703, h2710, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2712 | h2712
              · linarith only [h1, h2153, h2703, h2712, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2714 | h2714
                · linarith only [h0, h2340, h2704, h2714, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2716 | h2716
                  · rcases h0bigk with h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [hlam, p2717_0]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      rcases p2717_3 (m.d 0 1) (by simp) with h2720 | h2720
                      · rcases p2717_3 (m.d 0 2) (by simp) with h2721 | h2721
                        · linarith only [h0, h2721, hlam]
                        · linarith only [h2721, h4, hlam]
                      · linarith only [h1, h2720, hlam]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      rcases p2717_3 (m.d 0 1) (by simp) with h2725 | h2725
                      · rcases p2717_3 (m.d 0 2) (by simp) with h2726 | h2726
                        · linarith only [h0, h2726, hlam]
                        · linarith only [h2726, h5, hlam]
                      · linarith only [h2, h2725, hlam]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      rcases p2717_3 (m.d 0 1) (by simp) with h2730 | h2730
                      · rcases p2717_3 (m.d 0 2) (by simp) with h2731 | h2731
                        · linarith only [h0, h2731, hlam]
                        · linarith only [h2731, h6, hlam]
                      · linarith only [h2730, h3, hlam]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h0, hlam, p2717_0]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [hlam, p2717_0]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      rcases p2717_3 (m.d 0 1) (by simp) with h2737 | h2737
                      · rcases p2717_3 (m.d 0 2) (by simp) with h2738 | h2738
                        · rcases p2717_3 (m.d 0 3) (by simp) with h2739 | h2739
                          · linarith only [h2739, h4, hlam]
                          · rcases p2717_3 (m.d 0 4) (by simp) with h2741 | h2741
                            · linarith only [h2741, h5, hlam]
                            · linarith only [h2741, h7, hlam]
                        · linarith only [h2738, h4, hlam]
                      · linarith only [h1, h2737, hlam]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      rcases p2717_3 (m.d 0 1) (by simp) with h2746 | h2746
                      · rcases p2717_3 (m.d 0 2) (by simp) with h2747 | h2747
                        · rcases p2717_3 (m.d 0 3) (by simp) with h2748 | h2748
                          · linarith only [h2748, h4, hlam]
                          · rcases p2717_3 (m.d 0 4) (by simp) with h2750 | h2750
                            · linarith only [h2750, h5, hlam]
                            · rcases p2717_3 (m.d 0 5) (by simp) with h2752 | h2752
                              · linarith only [h2752, h6, hlam]
                              · linarith only [h2340, h2752, hlam]
                        · linarith only [h2747, h5, hlam]
                      · linarith only [h2, h2746, hlam]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      rcases p2717_3 (m.d 0 1) (by simp) with h2757 | h2757
                      · rcases p2717_3 (m.d 0 2) (by simp) with h2758 | h2758
                        · rcases p2717_3 (m.d 0 3) (by simp) with h2759 | h2759
                          · linarith only [h2759, h4, hlam]
                          · rcases p2717_3 (m.d 0 4) (by simp) with h2761 | h2761
                            · linarith only [h2761, h5, hlam]
                            · rcases p2717_3 (m.d 0 5) (by simp) with h2763 | h2763
                              · linarith only [h2763, h6, hlam]
                              · rcases h0emin with h2765 | h2765 | h2765 | h2765 | h2765
                                · rcases h2bigk with h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c | h2766c
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    rcases p2766_3 (m.d 0 2) (by simp) with h2768 | h2768
                                    · rcases p2766_3 (m.d 1 2) (by simp) with h2769 | h2769
                                      · linarith only [h0, h2769, hlam]
                                      · rcases p2766_3 (m.d 2 3) (by simp) with h2771 | h2771
                                        · linarith only [h2771, h4, hlam]
                                        · rcases p2766_3 (m.d 2 4) (by simp) with h2773 | h2773
                                          · linarith only [h2773, h5, hlam]
                                          · rcases p2766_3 (m.d 2 5) (by simp) with h2775 | h2775
                                            · linarith only [h2775, h6, hlam]
                                            · rcases h4bigk with h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c | h2777c
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [hlam, p2777_0]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h2340, h2703, h2706, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1, p2777_1]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h0, h2340, h2710, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1, p2777_1]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h7, hlam, p2777_0]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h2340, hlam, p2777_0]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h2, hlam, p2777_1]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [hlam, p2777_0]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h0, h2, h2340, h2710, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1, p2777_1]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h2706, hlam, p2777_1]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h2708, hlam, p2777_0]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h5, hlam, p2777_1]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h2704, hlam, p2777_1]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [hlam, p2777_0]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h2710, hlam, p2777_1]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h2714, hlam, p2777_0]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                rcases p2777_3 (m.d 0 4) (by simp) with h2793 | h2793
                                                · linarith only [h2793, h7, hlam]
                                                · rcases p2777_3 (m.d 1 4) (by simp) with h2795 | h2795
                                                  · linarith only [h2706, h2795, hlam]
                                                  · rcases p2777_3 (m.d 2 4) (by simp) with h2797 | h2797
                                                    · linarith only [h2710, h2797, hlam]
                                                    · rcases p2777_3 (m.d 3 4) (by simp) with h2799 | h2799
                                                      · rcases p2777_3 (m.d 4 5) (by simp) with h2800 | h2800
                                                        · linarith only [h2716, h2800, hlam]
                                                        · linarith only [h2340, h2800, hlam]
                                                      · linarith only [h2799, h7, hlam]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                rcases p2777_3 (m.d 0 4) (by simp) with h2804 | h2804
                                                · linarith only [h2804, h7, hlam]
                                                · linarith only [h2, h2804, hlam]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                rcases p2777_3 (m.d 0 4) (by simp) with h2807 | h2807
                                                · linarith only [h2807, h7, hlam]
                                                · linarith only [h2807, h5, hlam]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [hlam, p2777_0]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h2340, h2710, h5, hc23, hc34, hlam, hphi, p2777_1]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h1, h2703, h2716, h7, hc23, hc34, hlam, hphi, p2777_1]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h2703, h2706, h2716, hc23, hc34, hlam, hphi, p2777_1]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h2710, h2716, hc23, hc34, hlam, hphi, p2777_1]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [h2716, hlam, p2777_0]
                                              · have p2777_0 := h2777c.1
                                                have p2777_1 := h2777c.2.1
                                                have p2777_2 := h2777c.2.2.1
                                                have p2777_3 := h2777c.2.2.2
                                                linarith only [hlam, p2777_0]
                                    · linarith only [h0, h2768, hlam]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h1, h2340, h2703, h7, hlam, p2717_1, p2766_2]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h2340, h5, hlam, p2717_1, p2766_2]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h2705, h3, hlam, p2717_1, p2766_2]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h0, hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    rcases p2766_3 (m.d 0 2) (by simp) with h2823 | h2823
                                    · rcases p2766_3 (m.d 1 2) (by simp) with h2824 | h2824
                                      · rcases p2766_3 (m.d 2 3) (by simp) with h2825 | h2825
                                        · linarith only [h2825, hlam, p2766_0]
                                        · rcases p2766_3 (m.d 2 4) (by simp) with h2827 | h2827
                                          · linarith only [h2704, h2827, hlam]
                                          · linarith only [h2710, h2827, hlam]
                                      · linarith only [h2824, hlam, p2766_0]
                                    · linarith only [h2823, h4, hlam]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    rcases p2766_3 (m.d 0 2) (by simp) with h2832 | h2832
                                    · rcases p2766_3 (m.d 1 2) (by simp) with h2833 | h2833
                                      · rcases p2766_3 (m.d 2 3) (by simp) with h2834 | h2834
                                        · linarith only [h2703, h2834, hlam]
                                        · rcases p2766_3 (m.d 2 4) (by simp) with h2836 | h2836
                                          · linarith only [h2836, hlam, p2766_0]
                                          · rcases p2766_3 (m.d 2 5) (by simp) with h2838 | h2838
                                            · linarith only [h2705, h2838, hlam]
                                            · linarith only [h2714, h2838, hlam]
                                      · linarith only [h2833, hlam, p2766_0]
                                    · linarith only [h2832, h5, hlam]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    rcases p2766_3 (m.d 0 2) (by simp) with h2843 | h2843
                                    · rcases p2766_3 (m.d 1 2) (by simp) with h2844 | h2844
                                      · rcases p2766_3 (m.d 2 3) (by simp) with h2845 | h2845
                                        · linarith only [h2703, h2845, hlam]
                                        · rcases p2766_3 (m.d 2 4) (by simp) with h2847 | h2847
                                          · linarith only [h2704, h2847, hlam]
                                          · rcases p2766_3 (m.d 2 5) (by simp) with h2849 | h2849
                                            · linarith only [h2849, hlam, p2766_0]
                                            · rcases h4bigk with h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c | h2851c
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [hlam, p2851_0]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h0, h2340, h2703, h2706, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1, p2851_1]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h0, h2340, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2717_1, p2851_1]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h7, hlam, p2851_0]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h2340, hlam, p2851_0]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h2, hlam, p2851_1]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [hlam, p2851_0]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h0, h2, h2340, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2717_1, p2851_1]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h2706, hlam, p2851_1]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h2708, hlam, p2851_0]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h5, hlam, p2851_1]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h2704, hlam, p2851_1]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [hlam, p2851_0]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h2710, hlam, p2851_1]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h2714, hlam, p2851_0]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                rcases p2851_3 (m.d 0 4) (by simp) with h2867 | h2867
                                                · linarith only [h2867, h7, hlam]
                                                · rcases p2851_3 (m.d 1 4) (by simp) with h2869 | h2869
                                                  · linarith only [h2706, h2869, hlam]
                                                  · rcases p2851_3 (m.d 2 4) (by simp) with h2871 | h2871
                                                    · linarith only [h2710, h2871, hlam]
                                                    · rcases p2851_3 (m.d 3 4) (by simp) with h2873 | h2873
                                                      · rcases p2851_3 (m.d 4 5) (by simp) with h2874 | h2874
                                                        · linarith only [h2716, h2874, hlam]
                                                        · linarith only [h2340, h2874, hlam]
                                                      · linarith only [h2873, h7, hlam]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                rcases p2851_3 (m.d 0 4) (by simp) with h2878 | h2878
                                                · linarith only [h2878, h7, hlam]
                                                · linarith only [h2, h2878, hlam]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                rcases p2851_3 (m.d 0 4) (by simp) with h2881 | h2881
                                                · linarith only [h2881, h7, hlam]
                                                · linarith only [h2881, h5, hlam]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [hlam, p2851_0]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h2340, h7, hc03, hc34, hlam, hphi, p2851_1]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h1, h2703, h2716, h7, hc23, hc34, hlam, hphi, p2851_1]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h2704, h2710, h2716, hc23, hc34, hlam, hphi, p2851_1]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h2710, h2716, hc23, hc34, hlam, hphi, p2851_1]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [h2716, hlam, p2851_0]
                                              · have p2851_0 := h2851c.1
                                                have p2851_1 := h2851c.2.1
                                                have p2851_2 := h2851c.2.2.1
                                                have p2851_3 := h2851c.2.2.2
                                                linarith only [hlam, p2851_0]
                                      · linarith only [h2844, hlam, p2766_0]
                                    · linarith only [h2843, h6, hlam]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h4, hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h2703, hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h2710, hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h2712, hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h5, hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h2704, hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h0, h2714, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1, p2766_1]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h2714, hlam, p2766_1]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h6, hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h2705, hlam, p2766_0]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h0, h2705, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1, p2766_1]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [h0, h2705, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2717_1, p2766_1]
                                  · have p2766_0 := h2766c.1
                                    have p2766_1 := h2766c.2.1
                                    have p2766_2 := h2766c.2.2.1
                                    have p2766_3 := h2766c.2.2.2
                                    linarith only [hlam, p2766_0]
                                · rcases h2bigk with h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    rcases p2908_3 (m.d 0 2) (by simp) with h2910 | h2910
                                    · rcases p2908_3 (m.d 1 2) (by simp) with h2911 | h2911
                                      · linarith only [h0, h2911, hlam]
                                      · rcases p2908_3 (m.d 2 3) (by simp) with h2913 | h2913
                                        · linarith only [h2913, h4, hlam]
                                        · rcases p2908_3 (m.d 2 4) (by simp) with h2915 | h2915
                                          · linarith only [h2915, h5, hlam]
                                          · rcases p2908_3 (m.d 2 5) (by simp) with h2917 | h2917
                                            · linarith only [h2917, h6, hlam]
                                            · rcases h4bigk with h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [hlam, p2919_0]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h0, h2340, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2717_1, p2919_1]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h0, h2340, h2710, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1, p2919_1]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h7, hlam, p2919_0]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h2340, hlam, p2919_0]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h2, hlam, p2919_1]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [hlam, p2919_0]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h0, h2, h2340, h2710, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1, p2919_1]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h2706, hlam, p2919_1]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h2708, hlam, p2919_0]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h5, hlam, p2919_1]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h2704, hlam, p2919_1]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [hlam, p2919_0]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h2710, hlam, p2919_1]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h2714, hlam, p2919_0]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                rcases p2919_3 (m.d 0 4) (by simp) with h2935 | h2935
                                                · linarith only [h2935, h7, hlam]
                                                · rcases p2919_3 (m.d 1 4) (by simp) with h2937 | h2937
                                                  · linarith only [h2706, h2937, hlam]
                                                  · rcases p2919_3 (m.d 2 4) (by simp) with h2939 | h2939
                                                    · linarith only [h2710, h2939, hlam]
                                                    · rcases p2919_3 (m.d 3 4) (by simp) with h2941 | h2941
                                                      · rcases p2919_3 (m.d 4 5) (by simp) with h2942 | h2942
                                                        · linarith only [h2716, h2942, hlam]
                                                        · linarith only [h2340, h2942, hlam]
                                                      · linarith only [h2941, h7, hlam]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                rcases p2919_3 (m.d 0 4) (by simp) with h2946 | h2946
                                                · linarith only [h2946, h7, hlam]
                                                · linarith only [h2, h2946, hlam]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                rcases p2919_3 (m.d 0 4) (by simp) with h2949 | h2949
                                                · linarith only [h2949, h7, hlam]
                                                · linarith only [h2949, h5, hlam]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [hlam, p2919_0]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h2340, h2710, h5, hc23, hc34, hlam, hphi, p2919_1]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h1, h2703, h2716, h7, hc23, hc34, hlam, hphi, p2919_1]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h2704, h2710, h2716, hc23, hc34, hlam, hphi, p2919_1]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h2710, h2716, hc23, hc34, hlam, hphi, p2919_1]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [h2716, hlam, p2919_0]
                                              · have p2919_0 := h2919c.1
                                                have p2919_1 := h2919c.2.1
                                                have p2919_2 := h2919c.2.2.1
                                                have p2919_3 := h2919c.2.2.2
                                                linarith only [hlam, p2919_0]
                                    · linarith only [h0, h2910, hlam]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h1, h2340, h2703, h7, hlam, p2717_1, p2908_2]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h2, h2340, h2704, hlam, p2717_1, p2908_2]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h2705, h3, hlam, p2717_1, p2908_2]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h0, hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    rcases p2908_3 (m.d 0 2) (by simp) with h2965 | h2965
                                    · rcases p2908_3 (m.d 1 2) (by simp) with h2966 | h2966
                                      · rcases p2908_3 (m.d 2 3) (by simp) with h2967 | h2967
                                        · linarith only [h2967, hlam, p2908_0]
                                        · rcases p2908_3 (m.d 2 4) (by simp) with h2969 | h2969
                                          · linarith only [h2704, h2969, hlam]
                                          · linarith only [h2710, h2969, hlam]
                                      · linarith only [h2966, hlam, p2908_0]
                                    · linarith only [h2965, h4, hlam]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    rcases p2908_3 (m.d 0 2) (by simp) with h2974 | h2974
                                    · rcases p2908_3 (m.d 1 2) (by simp) with h2975 | h2975
                                      · rcases p2908_3 (m.d 2 3) (by simp) with h2976 | h2976
                                        · linarith only [h2703, h2976, hlam]
                                        · rcases p2908_3 (m.d 2 4) (by simp) with h2978 | h2978
                                          · linarith only [h2978, hlam, p2908_0]
                                          · rcases p2908_3 (m.d 2 5) (by simp) with h2980 | h2980
                                            · linarith only [h2705, h2980, hlam]
                                            · linarith only [h2714, h2980, hlam]
                                      · linarith only [h2975, hlam, p2908_0]
                                    · linarith only [h2974, h5, hlam]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    rcases p2908_3 (m.d 0 2) (by simp) with h2985 | h2985
                                    · rcases p2908_3 (m.d 1 2) (by simp) with h2986 | h2986
                                      · rcases p2908_3 (m.d 2 3) (by simp) with h2987 | h2987
                                        · linarith only [h2703, h2987, hlam]
                                        · rcases p2908_3 (m.d 2 4) (by simp) with h2989 | h2989
                                          · linarith only [h2704, h2989, hlam]
                                          · rcases p2908_3 (m.d 2 5) (by simp) with h2991 | h2991
                                            · linarith only [h2991, hlam, p2908_0]
                                            · rcases h4bigk with h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c | h2993c
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [hlam, p2993_0]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h0, h2340, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2717_1, p2993_1]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h0, h2340, h2710, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1, p2993_1]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h7, hlam, p2993_0]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h2340, hlam, p2993_0]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h2, hlam, p2993_1]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [hlam, p2993_0]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h0, h2, h2340, h2710, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1, p2993_1]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h2706, hlam, p2993_1]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h2708, hlam, p2993_0]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h5, hlam, p2993_1]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h2704, hlam, p2993_1]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [hlam, p2993_0]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h2710, hlam, p2993_1]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h2714, hlam, p2993_0]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                rcases p2993_3 (m.d 0 4) (by simp) with h3009 | h3009
                                                · linarith only [h3009, h7, hlam]
                                                · rcases p2993_3 (m.d 1 4) (by simp) with h3011 | h3011
                                                  · linarith only [h2706, h3011, hlam]
                                                  · rcases p2993_3 (m.d 2 4) (by simp) with h3013 | h3013
                                                    · linarith only [h2710, h3013, hlam]
                                                    · rcases p2993_3 (m.d 3 4) (by simp) with h3015 | h3015
                                                      · rcases p2993_3 (m.d 4 5) (by simp) with h3016 | h3016
                                                        · linarith only [h2716, h3016, hlam]
                                                        · linarith only [h2340, h3016, hlam]
                                                      · linarith only [h3015, h7, hlam]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                rcases p2993_3 (m.d 0 4) (by simp) with h3020 | h3020
                                                · linarith only [h3020, h7, hlam]
                                                · linarith only [h2, h3020, hlam]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                rcases p2993_3 (m.d 0 4) (by simp) with h3023 | h3023
                                                · linarith only [h3023, h7, hlam]
                                                · linarith only [h3023, h5, hlam]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [hlam, p2993_0]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h2340, h7, hc03, hc34, hlam, hphi, p2993_1]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h1, h2703, h2716, h7, hc23, hc34, hlam, hphi, p2993_1]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h2704, h2710, h2716, hc23, hc34, hlam, hphi, p2993_1]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h2710, h2716, hc23, hc34, hlam, hphi, p2993_1]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [h2716, hlam, p2993_0]
                                              · have p2993_0 := h2993c.1
                                                have p2993_1 := h2993c.2.1
                                                have p2993_2 := h2993c.2.2.1
                                                have p2993_3 := h2993c.2.2.2
                                                linarith only [hlam, p2993_0]
                                      · linarith only [h2986, hlam, p2908_0]
                                    · linarith only [h2985, h6, hlam]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h4, hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h2703, hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h2710, hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h2712, hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h5, hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h2704, hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h0, h2, h2340, h2704, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1, p2908_1]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h2714, hlam, p2908_1]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h6, hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h2705, hlam, p2908_0]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h0, h2705, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1, p2908_1]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [h0, h2705, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2717_1, p2908_1]
                                  · have p2908_0 := h2908c.1
                                    have p2908_1 := h2908c.2.1
                                    have p2908_2 := h2908c.2.2.1
                                    have p2908_3 := h2908c.2.2.2
                                    linarith only [hlam, p2908_0]
                                · linarith only [h0, h2340, h2765, h7, hc01, hlam, p2717_1]
                                · linarith only [h0, h2340, h2765, hc01, hlam, p2717_1]
                                · linarith only [h0, h2765, hc01, hlam, p2717_1]
                        · linarith only [h2758, h6, hlam]
                      · linarith only [h2757, h3, hlam]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h1, hlam, p2717_1]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h4, hlam, p2717_1]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [hlam, p2717_0]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h7, hlam, p2717_1]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h2153, hlam, p2717_1]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h2, hlam, p2717_0]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h5, hlam, p2717_0]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h1, h2703, h7, hc23, hc34, hlam, hphi, p2717_1]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [hlam, p2717_0]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h2340, hlam, p2717_0]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h3, hlam, p2717_0]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h6, hlam, p2717_1]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h1, h2153, h2703, hc23, hc35, hlam, hphi, p2717_1]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [h1, h2153, h2703, h7, hc23, hc35, hlam, hphi, p2717_1]
                    · have p2717_0 := h2717c.1
                      have p2717_1 := h2717c.2.1
                      have p2717_2 := h2717c.2.2.1
                      have p2717_3 := h2717c.2.2.2
                      linarith only [hlam, p2717_0]
                  · rcases h0bigk with h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [hlam, p3070_0]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h0, h2705, hc01, hc25, hlam, hphi, ht0b, ht5b, p3070_1]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      rcases p3070_3 (m.d 0 1) (by simp) with h3073 | h3073
                      · rcases p3070_3 (m.d 0 2) (by simp) with h3074 | h3074
                        · linarith only [h0, h3074, hlam]
                        · linarith only [h3074, h4, hlam]
                      · linarith only [h1, h3073, hlam]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      rcases p3070_3 (m.d 0 1) (by simp) with h3078 | h3078
                      · rcases p3070_3 (m.d 0 2) (by simp) with h3079 | h3079
                        · linarith only [h0, h3079, hlam]
                        · linarith only [h3079, h5, hlam]
                      · linarith only [h2, h3078, hlam]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      rcases p3070_3 (m.d 0 1) (by simp) with h3083 | h3083
                      · rcases p3070_3 (m.d 0 2) (by simp) with h3084 | h3084
                        · linarith only [h0, h3084, hlam]
                        · linarith only [h3084, h6, hlam]
                      · linarith only [h3, h3083, hlam]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h0, hlam, p3070_0]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [hlam, p3070_0]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      rcases p3070_3 (m.d 0 1) (by simp) with h3090 | h3090
                      · rcases p3070_3 (m.d 0 2) (by simp) with h3091 | h3091
                        · rcases p3070_3 (m.d 0 3) (by simp) with h3092 | h3092
                          · linarith only [h3092, h4, hlam]
                          · rcases p3070_3 (m.d 0 4) (by simp) with h3094 | h3094
                            · linarith only [h3094, h5, hlam]
                            · linarith only [h3094, h7, hlam]
                        · linarith only [h3091, h4, hlam]
                      · linarith only [h1, h3090, hlam]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      rcases p3070_3 (m.d 0 1) (by simp) with h3099 | h3099
                      · rcases p3070_3 (m.d 0 2) (by simp) with h3100 | h3100
                        · rcases p3070_3 (m.d 0 3) (by simp) with h3101 | h3101
                          · linarith only [h3101, h4, hlam]
                          · rcases p3070_3 (m.d 0 4) (by simp) with h3103 | h3103
                            · linarith only [h3103, h5, hlam]
                            · rcases p3070_3 (m.d 0 5) (by simp) with h3105 | h3105
                              · linarith only [h3105, h6, hlam]
                              · linarith only [h2340, h3105, hlam]
                        · linarith only [h3100, h5, hlam]
                      · linarith only [h2, h3099, hlam]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      rcases p3070_3 (m.d 0 1) (by simp) with h3110 | h3110
                      · rcases p3070_3 (m.d 0 2) (by simp) with h3111 | h3111
                        · rcases p3070_3 (m.d 0 3) (by simp) with h3112 | h3112
                          · linarith only [h3112, h4, hlam]
                          · rcases p3070_3 (m.d 0 4) (by simp) with h3114 | h3114
                            · linarith only [h3114, h5, hlam]
                            · rcases p3070_3 (m.d 0 5) (by simp) with h3116 | h3116
                              · linarith only [h3116, h6, hlam]
                              · rcases h0emin with h3118 | h3118 | h3118 | h3118 | h3118
                                · rcases h2bigk with h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c | h3119c
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    rcases p3119_3 (m.d 0 2) (by simp) with h3121 | h3121
                                    · rcases p3119_3 (m.d 1 2) (by simp) with h3122 | h3122
                                      · linarith only [h0, h3122, hlam]
                                      · rcases p3119_3 (m.d 2 3) (by simp) with h3124 | h3124
                                        · linarith only [h3124, h4, hlam]
                                        · rcases p3119_3 (m.d 2 4) (by simp) with h3126 | h3126
                                          · linarith only [h3126, h5, hlam]
                                          · rcases p3119_3 (m.d 2 5) (by simp) with h3128 | h3128
                                            · linarith only [h3128, h6, hlam]
                                            · rcases h4bigk with h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c | h3130c
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [hlam, p3130_0]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2703, h2706, h2716, h7, hc23, hc45, hlam, hphi, ht34, p3130_1]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2710, h2716, h7, hc23, hc45, hlam, hphi, ht34, p3130_1]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h7, hlam, p3130_0]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2340, hlam, p3130_0]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2, hlam, p3130_1]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [hlam, p3130_0]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h0, h2, h2340, h2710, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3070_1, p3130_1]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2706, hlam, p3130_1]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2708, hlam, p3130_0]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h5, hlam, p3130_1]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2704, hlam, p3130_1]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [hlam, p3130_0]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2710, hlam, p3130_1]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2714, hlam, p3130_0]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2716, hc04, hc45, hlam, hphi, p3130_1]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2704, h2710, h2716, hc23, hc45, hlam, hphi, ht34, p3130_1]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2710, h2716, hc23, hc45, hlam, hphi, ht34, p3130_1]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [hlam, p3130_0]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h2716, hlam, p3130_0]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                rcases p3130_3 (m.d 0 4) (by simp) with h3151 | h3151
                                                · linarith only [h3151, hlam, p3130_0]
                                                · rcases p3130_3 (m.d 1 4) (by simp) with h3153 | h3153
                                                  · linarith only [h2708, h3153, hlam]
                                                  · rcases p3130_3 (m.d 2 4) (by simp) with h3155 | h3155
                                                    · linarith only [h2714, h3155, hlam]
                                                    · rcases p3130_3 (m.d 3 4) (by simp) with h3157 | h3157
                                                      · linarith only [h2716, h3157, hlam]
                                                      · linarith only [h3157, h7, hlam]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                rcases p3130_3 (m.d 0 4) (by simp) with h3160 | h3160
                                                · linarith only [h2340, h3160, hlam]
                                                · linarith only [h2, h3160, hlam]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                rcases p3130_3 (m.d 0 4) (by simp) with h3163 | h3163
                                                · linarith only [h2340, h3163, hlam]
                                                · linarith only [h3163, h5, hlam]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [h1, h2703, h7, hc23, hc45, hlam, hphi, ht34, p3130_1]
                                              · have p3130_0 := h3130c.1
                                                have p3130_1 := h3130c.2.1
                                                have p3130_2 := h3130c.2.2.1
                                                have p3130_3 := h3130c.2.2.2
                                                linarith only [hlam, p3130_0]
                                    · linarith only [h0, h3121, hlam]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h2710, h2714, h6, hlam, p3070_1, p3119_2]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h2714, h6, hlam, p3070_1, p3119_2]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h6, hlam, p3070_1, p3119_2]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h0, hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    rcases p3119_3 (m.d 0 2) (by simp) with h3174 | h3174
                                    · rcases p3119_3 (m.d 1 2) (by simp) with h3175 | h3175
                                      · rcases p3119_3 (m.d 2 3) (by simp) with h3176 | h3176
                                        · linarith only [h3176, hlam, p3119_0]
                                        · rcases p3119_3 (m.d 2 4) (by simp) with h3178 | h3178
                                          · linarith only [h2704, h3178, hlam]
                                          · linarith only [h2710, h3178, hlam]
                                      · linarith only [h3175, hlam, p3119_0]
                                    · linarith only [h3174, h4, hlam]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    rcases p3119_3 (m.d 0 2) (by simp) with h3183 | h3183
                                    · rcases p3119_3 (m.d 1 2) (by simp) with h3184 | h3184
                                      · rcases p3119_3 (m.d 2 3) (by simp) with h3185 | h3185
                                        · linarith only [h2703, h3185, hlam]
                                        · rcases p3119_3 (m.d 2 4) (by simp) with h3187 | h3187
                                          · linarith only [h3187, hlam, p3119_0]
                                          · rcases p3119_3 (m.d 2 5) (by simp) with h3189 | h3189
                                            · linarith only [h2705, h3189, hlam]
                                            · linarith only [h2714, h3189, hlam]
                                      · linarith only [h3184, hlam, p3119_0]
                                    · linarith only [h3183, h5, hlam]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    rcases p3119_3 (m.d 0 2) (by simp) with h3194 | h3194
                                    · rcases p3119_3 (m.d 1 2) (by simp) with h3195 | h3195
                                      · rcases p3119_3 (m.d 2 3) (by simp) with h3196 | h3196
                                        · linarith only [h2703, h3196, hlam]
                                        · rcases p3119_3 (m.d 2 4) (by simp) with h3198 | h3198
                                          · linarith only [h2704, h3198, hlam]
                                          · rcases p3119_3 (m.d 2 5) (by simp) with h3200 | h3200
                                            · linarith only [h3200, hlam, p3119_0]
                                            · rcases h4bigk with h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [hlam, p3202_0]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h2340, h2704, h2710, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3070_1, p3202_1]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h0, h2340, h2710, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3070_1, p3202_1]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h7, hlam, p3202_0]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h2340, hlam, p3202_0]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h2, hlam, p3202_1]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [hlam, p3202_0]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h0, h2, h2340, h2710, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3070_1, p3202_1]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h2706, hlam, p3202_1]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h2708, hlam, p3202_0]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h5, hlam, p3202_1]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h2704, hlam, p3202_1]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [hlam, p3202_0]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h2710, hlam, p3202_1]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h2714, hlam, p3202_0]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h2716, hc04, hc45, hlam, hphi, p3202_1]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h2704, h2710, h2716, hc23, hc45, hlam, hphi, ht34, p3202_1]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h2710, h2716, hc23, hc45, hlam, hphi, ht34, p3202_1]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [hlam, p3202_0]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h2716, hlam, p3202_0]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                rcases p3202_3 (m.d 0 4) (by simp) with h3223 | h3223
                                                · linarith only [h3223, hlam, p3202_0]
                                                · rcases p3202_3 (m.d 1 4) (by simp) with h3225 | h3225
                                                  · linarith only [h2708, h3225, hlam]
                                                  · rcases p3202_3 (m.d 2 4) (by simp) with h3227 | h3227
                                                    · linarith only [h2714, h3227, hlam]
                                                    · rcases p3202_3 (m.d 3 4) (by simp) with h3229 | h3229
                                                      · linarith only [h2716, h3229, hlam]
                                                      · linarith only [h3229, h7, hlam]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                rcases p3202_3 (m.d 0 4) (by simp) with h3232 | h3232
                                                · linarith only [h2340, h3232, hlam]
                                                · linarith only [h2, h3232, hlam]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                rcases p3202_3 (m.d 0 4) (by simp) with h3235 | h3235
                                                · linarith only [h2340, h3235, hlam]
                                                · linarith only [h3235, h5, hlam]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [h1, h2703, h7, hc23, hc45, hlam, hphi, ht34, p3202_1]
                                              · have p3202_0 := h3202c.1
                                                have p3202_1 := h3202c.2.1
                                                have p3202_2 := h3202c.2.2.1
                                                have p3202_3 := h3202c.2.2.2
                                                linarith only [hlam, p3202_0]
                                      · linarith only [h3195, hlam, p3119_0]
                                    · linarith only [h3194, h6, hlam]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h4, hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h2703, hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h2710, hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h2712, hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h5, hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h2704, hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h0, h2714, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3070_1, p3119_1]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h2714, hlam, p3119_1]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h6, hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h2705, hlam, p3119_0]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h0, h2705, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3070_1, p3119_1]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [h0, h2705, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3070_1, p3119_1]
                                  · have p3119_0 := h3119c.1
                                    have p3119_1 := h3119c.2.1
                                    have p3119_2 := h3119c.2.2.1
                                    have p3119_3 := h3119c.2.2.2
                                    linarith only [hlam, p3119_0]
                                · rcases h2bigk with h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    rcases p3257_3 (m.d 0 2) (by simp) with h3259 | h3259
                                    · rcases p3257_3 (m.d 1 2) (by simp) with h3260 | h3260
                                      · linarith only [h0, h3260, hlam]
                                      · rcases p3257_3 (m.d 2 3) (by simp) with h3262 | h3262
                                        · linarith only [h3262, h4, hlam]
                                        · rcases p3257_3 (m.d 2 4) (by simp) with h3264 | h3264
                                          · linarith only [h3264, h5, hlam]
                                          · rcases p3257_3 (m.d 2 5) (by simp) with h3266 | h3266
                                            · linarith only [h3266, h6, hlam]
                                            · rcases h4bigk with h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c | h3268c
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [hlam, p3268_0]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h0, h2340, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3070_1, p3268_1]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h0, h2340, h2710, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3070_1, p3268_1]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h7, hlam, p3268_0]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h2340, hlam, p3268_0]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h2, hlam, p3268_1]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [hlam, p3268_0]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h0, h2, h2340, h2710, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3070_1, p3268_1]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h2706, hlam, p3268_1]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h2708, hlam, p3268_0]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h5, hlam, p3268_1]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h2704, hlam, p3268_1]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [hlam, p3268_0]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h2710, hlam, p3268_1]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h2714, hlam, p3268_0]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h2716, hc04, hc45, hlam, hphi, p3268_1]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h2704, h2710, h2716, hc23, hc45, hlam, hphi, ht34, p3268_1]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h2710, h2716, hc23, hc45, hlam, hphi, ht34, p3268_1]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [hlam, p3268_0]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h2716, hlam, p3268_0]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                rcases p3268_3 (m.d 0 4) (by simp) with h3289 | h3289
                                                · linarith only [h3289, hlam, p3268_0]
                                                · rcases p3268_3 (m.d 1 4) (by simp) with h3291 | h3291
                                                  · linarith only [h2708, h3291, hlam]
                                                  · rcases p3268_3 (m.d 2 4) (by simp) with h3293 | h3293
                                                    · linarith only [h2714, h3293, hlam]
                                                    · rcases p3268_3 (m.d 3 4) (by simp) with h3295 | h3295
                                                      · linarith only [h2716, h3295, hlam]
                                                      · linarith only [h3295, h7, hlam]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                rcases p3268_3 (m.d 0 4) (by simp) with h3298 | h3298
                                                · linarith only [h2340, h3298, hlam]
                                                · linarith only [h2, h3298, hlam]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                rcases p3268_3 (m.d 0 4) (by simp) with h3301 | h3301
                                                · linarith only [h2340, h3301, hlam]
                                                · linarith only [h3301, h5, hlam]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [h1, h2703, h7, hc23, hc45, hlam, hphi, ht34, p3268_1]
                                              · have p3268_0 := h3268c.1
                                                have p3268_1 := h3268c.2.1
                                                have p3268_2 := h3268c.2.2.1
                                                have p3268_3 := h3268c.2.2.2
                                                linarith only [hlam, p3268_0]
                                    · linarith only [h0, h3259, hlam]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h1, h2153, h2703, hlam, p3070_1, p3257_2]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h2, h2340, h2704, hlam, p3070_1, p3257_2]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h2705, h3, hlam, p3070_1, p3257_2]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h0, hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    rcases p3257_3 (m.d 0 2) (by simp) with h3312 | h3312
                                    · rcases p3257_3 (m.d 1 2) (by simp) with h3313 | h3313
                                      · rcases p3257_3 (m.d 2 3) (by simp) with h3314 | h3314
                                        · linarith only [h3314, hlam, p3257_0]
                                        · rcases p3257_3 (m.d 2 4) (by simp) with h3316 | h3316
                                          · linarith only [h2704, h3316, hlam]
                                          · linarith only [h2710, h3316, hlam]
                                      · linarith only [h3313, hlam, p3257_0]
                                    · linarith only [h3312, h4, hlam]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    rcases p3257_3 (m.d 0 2) (by simp) with h3321 | h3321
                                    · rcases p3257_3 (m.d 1 2) (by simp) with h3322 | h3322
                                      · rcases p3257_3 (m.d 2 3) (by simp) with h3323 | h3323
                                        · linarith only [h2703, h3323, hlam]
                                        · rcases p3257_3 (m.d 2 4) (by simp) with h3325 | h3325
                                          · linarith only [h3325, hlam, p3257_0]
                                          · rcases p3257_3 (m.d 2 5) (by simp) with h3327 | h3327
                                            · linarith only [h2705, h3327, hlam]
                                            · linarith only [h2714, h3327, hlam]
                                      · linarith only [h3322, hlam, p3257_0]
                                    · linarith only [h3321, h5, hlam]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    rcases p3257_3 (m.d 0 2) (by simp) with h3332 | h3332
                                    · rcases p3257_3 (m.d 1 2) (by simp) with h3333 | h3333
                                      · rcases p3257_3 (m.d 2 3) (by simp) with h3334 | h3334
                                        · linarith only [h2703, h3334, hlam]
                                        · rcases p3257_3 (m.d 2 4) (by simp) with h3336 | h3336
                                          · linarith only [h2704, h3336, hlam]
                                          · rcases p3257_3 (m.d 2 5) (by simp) with h3338 | h3338
                                            · linarith only [h3338, hlam, p3257_0]
                                            · rcases h4bigk with h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [hlam, p3340_0]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h2340, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p3070_1, p3340_1]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h0, h2340, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3070_1, p3340_1]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h7, hlam, p3340_0]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h2340, hlam, p3340_0]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h2, hlam, p3340_1]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [hlam, p3340_0]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h0, h2, h2340, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3070_1, p3340_1]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h2706, hlam, p3340_1]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h2708, hlam, p3340_0]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h5, hlam, p3340_1]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h2704, hlam, p3340_1]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [hlam, p3340_0]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h2710, hlam, p3340_1]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h2714, hlam, p3340_0]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h1, h2703, h2716, h7, hc23, hc45, hlam, hphi, ht34, p3340_1]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h2716, hc14, hc45, hlam, hphi, p3340_1]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h2710, h2716, hc23, hc45, hlam, hphi, ht34, p3340_1]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [hlam, p3340_0]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h2716, hlam, p3340_0]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                rcases p3340_3 (m.d 0 4) (by simp) with h3361 | h3361
                                                · linarith only [h3361, hlam, p3340_0]
                                                · rcases p3340_3 (m.d 1 4) (by simp) with h3363 | h3363
                                                  · linarith only [h2708, h3363, hlam]
                                                  · rcases p3340_3 (m.d 2 4) (by simp) with h3365 | h3365
                                                    · linarith only [h2714, h3365, hlam]
                                                    · rcases p3340_3 (m.d 3 4) (by simp) with h3367 | h3367
                                                      · linarith only [h2716, h3367, hlam]
                                                      · linarith only [h3367, h7, hlam]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                rcases p3340_3 (m.d 0 4) (by simp) with h3370 | h3370
                                                · linarith only [h2340, h3370, hlam]
                                                · linarith only [h2, h3370, hlam]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                rcases p3340_3 (m.d 0 4) (by simp) with h3373 | h3373
                                                · linarith only [h2340, h3373, hlam]
                                                · linarith only [h3373, h5, hlam]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [h1, h2703, h7, hc23, hc45, hlam, hphi, ht34, p3340_1]
                                              · have p3340_0 := h3340c.1
                                                have p3340_1 := h3340c.2.1
                                                have p3340_2 := h3340c.2.2.1
                                                have p3340_3 := h3340c.2.2.2
                                                linarith only [hlam, p3340_0]
                                      · linarith only [h3333, hlam, p3257_0]
                                    · linarith only [h3332, h6, hlam]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h4, hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h2703, hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h2710, hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h2712, hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h5, hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h2704, hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h0, h2, h2340, h2704, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3070_1, p3257_1]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h2714, hlam, p3257_1]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h6, hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h2705, hlam, p3257_0]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h0, h2705, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3070_1, p3257_1]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [h0, h2705, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3070_1, p3257_1]
                                  · have p3257_0 := h3257c.1
                                    have p3257_1 := h3257c.2.1
                                    have p3257_2 := h3257c.2.2.1
                                    have p3257_3 := h3257c.2.2.2
                                    linarith only [hlam, p3257_0]
                                · linarith only [h0, h2340, h3118, h7, hc01, hlam, p3070_1]
                                · linarith only [h0, h2340, h3118, hc01, hlam, p3070_1]
                                · linarith only [h0, h3118, hc01, hlam, p3070_1]
                        · linarith only [h3111, h6, hlam]
                      · linarith only [h3, h3110, hlam]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h1, hlam, p3070_1]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h4, hlam, p3070_1]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [hlam, p3070_0]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h7, hlam, p3070_1]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h2153, hlam, p3070_1]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h2, hlam, p3070_0]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h5, hlam, p3070_0]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h1, h7, hc13, hc34, hlam, hphi, p3070_1]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [hlam, p3070_0]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h2340, hlam, p3070_0]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h3, hlam, p3070_0]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h6, hlam, p3070_1]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h1, h2153, h2716, hc13, hc45, hlam, hphi, ht34, p3070_1]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [h2153, h2716, hc04, hc45, hlam, hphi, p3070_1]
                    · have p3070_0 := h3070c.1
                      have p3070_1 := h3070c.2.1
                      have p3070_2 := h3070c.2.2.1
                      have p3070_3 := h3070c.2.2.2
                      linarith only [hlam, p3070_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3415 | h3415
        · linarith only [h1, h3415, h7, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3417 | h3417
          · linarith only [h2, h2340, h3417, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3419 | h3419
            · linarith only [h2703, h2705, h3419, h6, h7, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3421 | h3421
              · linarith only [h1, h2153, h2703, h3421, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3423 | h3423
                · linarith only [h0, h2340, h2704, h2705, h3423, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3425 | h3425
                  · linarith only [h2340, h2704, h2705, h3419, h3425, h6, hc23, hc34, hlam, hphi]
                  · rcases h0bigk with h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c | h3427c
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [hlam, p3427_0]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h0, h2704, h3419, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3427_1]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      rcases p3427_3 (m.d 0 1) (by simp) with h3430 | h3430
                      · rcases p3427_3 (m.d 0 2) (by simp) with h3431 | h3431
                        · linarith only [h0, h3431, hlam]
                        · linarith only [h3431, h4, hlam]
                      · linarith only [h1, h3430, hlam]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      rcases p3427_3 (m.d 0 1) (by simp) with h3435 | h3435
                      · rcases p3427_3 (m.d 0 2) (by simp) with h3436 | h3436
                        · linarith only [h0, h3436, hlam]
                        · linarith only [h3436, h5, hlam]
                      · linarith only [h2, h3435, hlam]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h2704, h2705, h3419, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3427_1]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h0, hlam, p3427_0]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [hlam, p3427_0]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      rcases p3427_3 (m.d 0 1) (by simp) with h3443 | h3443
                      · rcases p3427_3 (m.d 0 2) (by simp) with h3444 | h3444
                        · rcases p3427_3 (m.d 0 3) (by simp) with h3445 | h3445
                          · linarith only [h3445, h4, hlam]
                          · rcases p3427_3 (m.d 0 4) (by simp) with h3447 | h3447
                            · linarith only [h3447, h5, hlam]
                            · linarith only [h3447, h7, hlam]
                        · linarith only [h3444, h4, hlam]
                      · linarith only [h1, h3443, hlam]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      rcases p3427_3 (m.d 0 1) (by simp) with h3452 | h3452
                      · rcases p3427_3 (m.d 0 2) (by simp) with h3453 | h3453
                        · rcases p3427_3 (m.d 0 3) (by simp) with h3454 | h3454
                          · linarith only [h3454, h4, hlam]
                          · rcases p3427_3 (m.d 0 4) (by simp) with h3456 | h3456
                            · linarith only [h3456, h5, hlam]
                            · rcases p3427_3 (m.d 0 5) (by simp) with h3458 | h3458
                              · linarith only [h3458, h6, hlam]
                              · linarith only [h2340, h3458, hlam]
                        · linarith only [h3453, h5, hlam]
                      · linarith only [h2, h3452, hlam]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h2704, h2705, h3419, h6, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3427_1]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h1, hlam, p3427_1]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h4, hlam, p3427_1]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [hlam, p3427_0]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h7, hlam, p3427_1]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h2153, hlam, p3427_1]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h2, hlam, p3427_0]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h5, hlam, p3427_0]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h7, hc03, hc34, hlam, hphi, p3427_1]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [hlam, p3427_0]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h2340, hlam, p3427_0]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h3, hlam, p3427_0]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h6, hlam, p3427_1]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h1, h2153, hc13, hc35, hlam, hphi, p3427_1]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [h2340, hc04, hc45, hlam, hphi, p3427_1]
                    · have p3427_0 := h3427c.1
                      have p3427_1 := h3427c.2.1
                      have p3427_2 := h3427c.2.2.1
                      have p3427_3 := h3427c.2.2.2
                      linarith only [hlam, p3427_0]
    · linarith only [h2340, h2703, h2704, h5, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h3480 | h3480
    · linarith only [h2340, h2703, h3480, h4, h7, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3482 | h3482
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3483 | h3483
        · linarith only [h2703, h3482, h3483, h4, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3485 | h3485
          · linarith only [h2340, h2703, h3482, h3485, h4, h7, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h3480, h3482, h3485, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3488 | h3488
        · linarith only [h2703, h3488, h4, h7, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3490 | h3490
          · linarith only [h2, h2340, h2703, h3490, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3492 | h3492
            · linarith only [h3492, h4, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3494 | h3494
              · linarith only [h2153, h3494, h4, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3496 | h3496
                · linarith only [h2340, h3496, h5, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3498 | h3498
                  · linarith only [h2340, h2703, h3498, h4, h7, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h2703, h3498, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6988000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s6_x1_x1 (m : N7Model)
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
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h2153 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h2340 | h2340
  · exact r1l7_20_12_14_H_I_L_I_L_I_s6_x1_x1_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h2153 h2340
  · exact r1l7_20_12_14_H_I_L_I_L_I_s6_x1_x1_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h2153 h2340

end R2N4
