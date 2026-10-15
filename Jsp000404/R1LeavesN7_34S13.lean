import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_34S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2086 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2336 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2407 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2408 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h2409 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 2 3 4 (by decide) (by decide) with h2771 | h2771
  · rcases m.htr 2 3 5 (by decide) (by decide) with h2772 | h2772
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2773 | h2773
      · rcases m.htr 3 4 5 (by decide) (by decide) with h2774 | h2774
        · linarith only [h2407, h2409, h2774, hlam]
        · rcases h1bigk with h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h0, h2086, h2409, h2771, h2773, h4, hlam, p2776_2]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            rcases p2776_3 (m.d 0 1) (by simp) with h2779 | h2779
            · rcases p2776_3 (m.d 1 2) (by simp) with h2780 | h2780
              · linarith only [h0, h2780, hlam]
              · rcases p2776_3 (m.d 1 3) (by simp) with h2782 | h2782
                · linarith only [h2782, hlam, p2776_0]
                · rcases p2776_3 (m.d 1 4) (by simp) with h2784 | h2784
                  · linarith only [h2, h2784, hlam]
                  · rcases p2776_3 (m.d 1 5) (by simp) with h2786 | h2786
                    · linarith only [h2786, h3, hlam]
                    · rcases h3bigk with h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        rcases p2788_3 (m.d 0 3) (by simp) with h2790 | h2790
                        · rcases p2788_3 (m.d 1 3) (by simp) with h2791 | h2791
                          · linarith only [h1, h2791, hlam]
                          · rcases p2788_3 (m.d 2 3) (by simp) with h2793 | h2793
                            · linarith only [h2793, h4, hlam]
                            · linarith only [h2793, h9, hlam]
                        · linarith only [h1, h2790, hlam]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h0, h2086, h2409, h2771, h2773, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2788_1]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        rcases p2788_3 (m.d 0 3) (by simp) with h2798 | h2798
                        · rcases p2788_3 (m.d 1 3) (by simp) with h2799 | h2799
                          · linarith only [h1, h2799, hlam]
                          · linarith only [h2407, h2799, hlam]
                        · linarith only [h2798, hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        rcases p2788_3 (m.d 0 3) (by simp) with h2803 | h2803
                        · rcases p2788_3 (m.d 1 3) (by simp) with h2804 | h2804
                          · linarith only [h1, h2804, hlam]
                          · linarith only [h2408, h2804, hlam]
                        · linarith only [h2803, hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h1, hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h9, hlam, p2788_1]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2776_1, p2788_1]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h2774, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2776_1, p2788_1]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h4, hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h0, h4, hlam, p2776_2, p2788_1]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        rcases p2788_3 (m.d 0 3) (by simp) with h2816 | h2816
                        · rcases p2788_3 (m.d 1 3) (by simp) with h2817 | h2817
                          · linarith only [h2817, h9, hlam]
                          · linarith only [h2407, h2817, hlam]
                        · linarith only [h2816, h6, hlam]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        rcases p2788_3 (m.d 0 3) (by simp) with h2821 | h2821
                        · rcases p2788_3 (m.d 1 3) (by simp) with h2822 | h2822
                          · linarith only [h2822, h9, hlam]
                          · linarith only [h2408, h2822, hlam]
                        · linarith only [h2821, h7, hlam]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h6, hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h2407, hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h2771, hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h2774, hlam, p2788_1]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h7, hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h2408, hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h2772, hlam, p2788_0]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [h2408, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2776_1, p2788_1]
                      · have p2788_0 := h2788c.1
                        have p2788_1 := h2788c.2.1
                        have p2788_2 := h2788c.2.2.1
                        have p2788_3 := h2788c.2.2.2
                        linarith only [hlam, p2788_0]
            · linarith only [h2779, hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h0, h2409, h2773, h5, hlam, p2776_2]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            rcases p2776_3 (m.d 0 1) (by simp) with h2838 | h2838
            · rcases p2776_3 (m.d 1 2) (by simp) with h2839 | h2839
              · linarith only [h0, h2839, hlam]
              · rcases p2776_3 (m.d 1 3) (by simp) with h2841 | h2841
                · linarith only [h1, h2841, hlam]
                · linarith only [h2408, h2841, hlam]
            · linarith only [h2838, hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h0, hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h9, hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h2086, hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h2336, hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h1, hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            rcases p2776_3 (m.d 0 1) (by simp) with h2851 | h2851
            · rcases p2776_3 (m.d 1 2) (by simp) with h2852 | h2852
              · linarith only [h2852, h9, hlam]
              · rcases p2776_3 (m.d 1 3) (by simp) with h2854 | h2854
                · rcases p2776_3 (m.d 1 4) (by simp) with h2855 | h2855
                  · linarith only [h2407, h2855, hlam]
                  · linarith only [h2086, h2855, hlam]
                · linarith only [h2854, h9, hlam]
            · linarith only [h0, h2851, hlam]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            rcases p2776_3 (m.d 0 1) (by simp) with h2861 | h2861
            · rcases p2776_3 (m.d 1 2) (by simp) with h2862 | h2862
              · linarith only [h2862, h9, hlam]
              · rcases p2776_3 (m.d 1 3) (by simp) with h2864 | h2864
                · rcases p2776_3 (m.d 1 4) (by simp) with h2865 | h2865
                  · linarith only [h2407, h2865, hlam]
                  · rcases p2776_3 (m.d 1 5) (by simp) with h2867 | h2867
                    · linarith only [h2408, h2867, hlam]
                    · linarith only [h2409, h2867, hlam]
                · linarith only [h2407, h2864, hlam]
            · linarith only [h2, h2861, hlam]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            rcases p2776_3 (m.d 0 1) (by simp) with h2872 | h2872
            · rcases p2776_3 (m.d 1 2) (by simp) with h2873 | h2873
              · linarith only [h2873, h9, hlam]
              · rcases p2776_3 (m.d 1 3) (by simp) with h2875 | h2875
                · rcases p2776_3 (m.d 1 4) (by simp) with h2876 | h2876
                  · linarith only [h2407, h2876, hlam]
                  · rcases p2776_3 (m.d 1 5) (by simp) with h2878 | h2878
                    · linarith only [h2408, h2878, hlam]
                    · rcases h3bigk with h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h2409, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p2776_1, p2880_1]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h0, h2409, h4, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2776_1, p2880_1]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        rcases p2880_3 (m.d 0 3) (by simp) with h2884 | h2884
                        · rcases p2880_3 (m.d 1 3) (by simp) with h2885 | h2885
                          · linarith only [h1, h2885, hlam]
                          · linarith only [h2407, h2885, hlam]
                        · linarith only [h2884, hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        rcases p2880_3 (m.d 0 3) (by simp) with h2889 | h2889
                        · rcases p2880_3 (m.d 1 3) (by simp) with h2890 | h2890
                          · linarith only [h1, h2890, hlam]
                          · linarith only [h2408, h2890, hlam]
                        · linarith only [h2889, hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h1, hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h9, hlam, p2880_1]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        rcases p2880_3 (m.d 0 3) (by simp) with h2897 | h2897
                        · rcases p2880_3 (m.d 1 3) (by simp) with h2898 | h2898
                          · rcases p2880_3 (m.d 2 3) (by simp) with h2899 | h2899
                            · rcases p2880_3 (m.d 3 4) (by simp) with h2900 | h2900
                              · linarith only [h2900, hlam, p2880_0]
                              · rcases p2880_3 (m.d 3 5) (by simp) with h2902 | h2902
                                · linarith only [h2408, h2902, hlam]
                                · linarith only [h2774, h2902, hlam]
                            · linarith only [h2771, h2899, hlam]
                          · linarith only [h2898, hlam, p2880_0]
                        · linarith only [h2897, h6, hlam]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        rcases p2880_3 (m.d 0 3) (by simp) with h2908 | h2908
                        · rcases p2880_3 (m.d 1 3) (by simp) with h2909 | h2909
                          · rcases p2880_3 (m.d 2 3) (by simp) with h2910 | h2910
                            · rcases p2880_3 (m.d 3 4) (by simp) with h2911 | h2911
                              · linarith only [h2407, h2911, hlam]
                              · rcases p2880_3 (m.d 3 5) (by simp) with h2913 | h2913
                                · linarith only [h2913, hlam, p2880_0]
                                · rcases h4bigk with h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [hlam, p2915_0]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    rcases p2915_3 (m.d 0 4) (by simp) with h2917 | h2917
                                    · rcases p2915_3 (m.d 1 4) (by simp) with h2918 | h2918
                                      · linarith only [h2, h2918, hlam]
                                      · rcases p2915_3 (m.d 2 4) (by simp) with h2920 | h2920
                                        · linarith only [h2920, h5, hlam]
                                        · linarith only [h2086, h2920, hlam]
                                    · linarith only [h2, h2917, hlam]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h0, h2086, h2409, h2773, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2915_1]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    rcases p2915_3 (m.d 0 4) (by simp) with h2925 | h2925
                                    · rcases p2915_3 (m.d 1 4) (by simp) with h2926 | h2926
                                      · linarith only [h2, h2926, hlam]
                                      · linarith only [h2407, h2926, hlam]
                                    · linarith only [h2925, h6, hlam]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    rcases p2915_3 (m.d 0 4) (by simp) with h2930 | h2930
                                    · rcases p2915_3 (m.d 1 4) (by simp) with h2931 | h2931
                                      · linarith only [h2, h2931, hlam]
                                      · rcases p2915_3 (m.d 2 4) (by simp) with h2933 | h2933
                                        · linarith only [h2933, h5, hlam]
                                        · linarith only [h2773, h2933, hlam]
                                    · linarith only [h2930, hlam, p2915_0]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h2, hlam, p2915_1]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [hlam, p2915_0]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h2086, hlam, p2915_0]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h2409, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2776_1, p2915_1]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h2409, hlam, p2915_0]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h5, hlam, p2915_1]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    rcases p2915_3 (m.d 0 4) (by simp) with h2943 | h2943
                                    · rcases p2915_3 (m.d 1 4) (by simp) with h2944 | h2944
                                      · linarith only [h2086, h2944, hlam]
                                      · rcases p2915_3 (m.d 2 4) (by simp) with h2946 | h2946
                                        · rcases p2915_3 (m.d 3 4) (by simp) with h2947 | h2947
                                          · linarith only [h2771, h2947, hlam]
                                          · rcases p2915_3 (m.d 4 5) (by simp) with h2949 | h2949
                                            · linarith only [h2773, h2949, hlam]
                                            · linarith only [h2409, h2949, hlam]
                                        · linarith only [h2086, h2946, hlam]
                                    · linarith only [h2, h2943, hlam]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [hlam, p2915_0]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    rcases p2915_3 (m.d 0 4) (by simp) with h2955 | h2955
                                    · rcases p2915_3 (m.d 1 4) (by simp) with h2956 | h2956
                                      · linarith only [h2086, h2956, hlam]
                                      · linarith only [h2407, h2956, hlam]
                                    · linarith only [h2955, h6, hlam]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h2086, h2409, hc12, hc24, hlam, hphi, p2915_1]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h6, hlam, p2915_1]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h2407, hlam, p2915_0]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h2771, hlam, p2915_0]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [hlam, p2915_0]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h2774, hlam, p2915_0]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h8, hlam, p2915_0]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h0, h2086, h2771, h2773, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2915_1]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h2773, hlam, p2915_0]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [h0, h2771, h2773, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2915_1]
                                  · have p2915_0 := h2915c.1
                                    have p2915_1 := h2915c.2.1
                                    have p2915_2 := h2915c.2.2.1
                                    have p2915_3 := h2915c.2.2.2
                                    linarith only [hlam, p2915_0]
                            · linarith only [h2772, h2910, hlam]
                          · linarith only [h2909, hlam, p2880_0]
                        · linarith only [h2908, h7, hlam]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h4, hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p2776_1, p2880_1]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        rcases p2880_3 (m.d 0 3) (by simp) with h2977 | h2977
                        · rcases p2880_3 (m.d 1 3) (by simp) with h2978 | h2978
                          · linarith only [h2978, h9, hlam]
                          · linarith only [h2407, h2978, hlam]
                        · linarith only [h2977, h6, hlam]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        rcases p2880_3 (m.d 0 3) (by simp) with h2982 | h2982
                        · rcases p2880_3 (m.d 1 3) (by simp) with h2983 | h2983
                          · linarith only [h2983, h9, hlam]
                          · linarith only [h2408, h2983, hlam]
                        · linarith only [h2982, h7, hlam]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h6, hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h2407, hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h2771, hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h2774, hlam, p2880_1]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h7, hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h2408, hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h2772, hlam, p2880_0]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [h1, h2408, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2880_1]
                      · have p2880_0 := h2880c.1
                        have p2880_1 := h2880c.2.1
                        have p2880_2 := h2880c.2.2.1
                        have p2880_3 := h2880c.2.2.2
                        linarith only [hlam, p2880_0]
                · linarith only [h2408, h2875, hlam]
            · linarith only [h2872, h3, hlam]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h2, hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h0, h2409, h2771, h2773, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2776_1]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h2407, hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h2409, hlam, p2776_1]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h3, hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h0, h2409, h2771, h2773, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2776_1]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h2408, hlam, p2776_0]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [h0, h2409, h2771, h2773, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2776_1]
          · have p2776_0 := h2776c.1
            have p2776_1 := h2776c.2.1
            have p2776_2 := h2776c.2.2.1
            have p2776_3 := h2776c.2.2.2
            linarith only [hlam, p2776_0]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3009 | h3009
        · linarith only [h0, h2086, h2773, h3009, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases h1bigk with h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c | h3011c
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [h0, h2086, h2773, h4, h6, h8, hlam, p3011_2]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            rcases p3011_3 (m.d 0 1) (by simp) with h3014 | h3014
            · rcases p3011_3 (m.d 1 2) (by simp) with h3015 | h3015
              · linarith only [h0, h3015, hlam]
              · rcases p3011_3 (m.d 1 3) (by simp) with h3017 | h3017
                · linarith only [h3017, hlam, p3011_0]
                · rcases p3011_3 (m.d 1 4) (by simp) with h3019 | h3019
                  · linarith only [h2, h3019, hlam]
                  · rcases p3011_3 (m.d 1 5) (by simp) with h3021 | h3021
                    · linarith only [h3, h3021, hlam]
                    · rcases h3bigk with h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        rcases p3023_3 (m.d 0 3) (by simp) with h3025 | h3025
                        · rcases p3023_3 (m.d 1 3) (by simp) with h3026 | h3026
                          · linarith only [h1, h3026, hlam]
                          · rcases p3023_3 (m.d 2 3) (by simp) with h3028 | h3028
                            · linarith only [h3028, h4, hlam]
                            · linarith only [h3028, h9, hlam]
                        · linarith only [h1, h3025, hlam]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        rcases p3023_3 (m.d 0 3) (by simp) with h3032 | h3032
                        · rcases p3023_3 (m.d 1 3) (by simp) with h3033 | h3033
                          · linarith only [h1, h3033, hlam]
                          · rcases p3023_3 (m.d 2 3) (by simp) with h3035 | h3035
                            · linarith only [h3035, h4, hlam]
                            · rcases p3023_3 (m.d 3 4) (by simp) with h3037 | h3037
                              · linarith only [h3037, h6, hlam]
                              · rcases p3023_3 (m.d 3 5) (by simp) with h3039 | h3039
                                · linarith only [h3039, h7, hlam]
                                · rcases h4bigk with h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [hlam, p3041_0]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    rcases p3041_3 (m.d 0 4) (by simp) with h3043 | h3043
                                    · rcases p3041_3 (m.d 1 4) (by simp) with h3044 | h3044
                                      · linarith only [h2, h3044, hlam]
                                      · rcases p3041_3 (m.d 2 4) (by simp) with h3046 | h3046
                                        · linarith only [h3046, h5, hlam]
                                        · linarith only [h2086, h3046, hlam]
                                    · linarith only [h2, h3043, hlam]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    rcases p3041_3 (m.d 0 4) (by simp) with h3050 | h3050
                                    · rcases p3041_3 (m.d 1 4) (by simp) with h3051 | h3051
                                      · linarith only [h2, h3051, hlam]
                                      · rcases p3041_3 (m.d 2 4) (by simp) with h3053 | h3053
                                        · linarith only [h3053, h5, hlam]
                                        · rcases p3041_3 (m.d 3 4) (by simp) with h3055 | h3055
                                          · linarith only [h3055, h6, hlam]
                                          · rcases p3041_3 (m.d 4 5) (by simp) with h3057 | h3057
                                            · linarith only [h3057, h8, hlam]
                                            · linarith only [h2773, h3057, hlam]
                                    · linarith only [h3050, h5, hlam]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    rcases p3041_3 (m.d 0 4) (by simp) with h3061 | h3061
                                    · rcases p3041_3 (m.d 1 4) (by simp) with h3062 | h3062
                                      · linarith only [h2, h3062, hlam]
                                      · linarith only [h2407, h3062, hlam]
                                    · linarith only [h3061, h6, hlam]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h2086, h2773, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3041_1]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h2, hlam, p3041_1]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [hlam, p3041_0]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h2086, hlam, p3041_0]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h2086, h2773, hc34, hc45, hlam, hphi, p3041_1]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h2409, hlam, p3041_0]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h5, hlam, p3041_1]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h2773, hc14, hc45, hlam, hphi, p3041_1]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [hlam, p3041_0]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h0, h2773, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3041_1]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h2773, hlam, p3041_0]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h6, hlam, p3041_1]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h2407, hlam, p3041_0]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h2771, hlam, p3041_0]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [hlam, p3041_0]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h3009, hlam, p3041_0]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h8, hlam, p3041_0]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    rcases p3041_3 (m.d 0 4) (by simp) with h3083 | h3083
                                    · rcases p3041_3 (m.d 1 4) (by simp) with h3084 | h3084
                                      · linarith only [h3084, hlam, p3041_0]
                                      · rcases p3041_3 (m.d 2 4) (by simp) with h3086 | h3086
                                        · linarith only [h2773, h3086, hlam]
                                        · linarith only [h2086, h3086, hlam]
                                    · linarith only [h2, h3083, hlam]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [h0, h2086, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3041_1]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    rcases p3041_3 (m.d 0 4) (by simp) with h3091 | h3091
                                    · rcases p3041_3 (m.d 1 4) (by simp) with h3092 | h3092
                                      · linarith only [h2409, h3092, hlam]
                                      · linarith only [h2407, h3092, hlam]
                                    · linarith only [h3091, h6, hlam]
                                  · have p3041_0 := h3041c.1
                                    have p3041_1 := h3041c.2.1
                                    have p3041_2 := h3041c.2.2.1
                                    have p3041_3 := h3041c.2.2.2
                                    linarith only [hlam, p3041_0]
                        · linarith only [h3032, h4, hlam]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        rcases p3023_3 (m.d 0 3) (by simp) with h3098 | h3098
                        · rcases p3023_3 (m.d 1 3) (by simp) with h3099 | h3099
                          · linarith only [h1, h3099, hlam]
                          · linarith only [h2407, h3099, hlam]
                        · linarith only [h3098, hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        rcases p3023_3 (m.d 0 3) (by simp) with h3103 | h3103
                        · rcases p3023_3 (m.d 1 3) (by simp) with h3104 | h3104
                          · linarith only [h1, h3104, hlam]
                          · linarith only [h2408, h3104, hlam]
                        · linarith only [h3103, hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h1, hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h9, hlam, p3023_1]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3011_1, p3023_1]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h3009, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3011_1, p3023_1]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h4, hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h0, h4, hlam, p3011_2, p3023_1]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        rcases p3023_3 (m.d 0 3) (by simp) with h3116 | h3116
                        · rcases p3023_3 (m.d 1 3) (by simp) with h3117 | h3117
                          · linarith only [h3117, h9, hlam]
                          · linarith only [h2407, h3117, hlam]
                        · linarith only [h3116, h6, hlam]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        rcases p3023_3 (m.d 0 3) (by simp) with h3121 | h3121
                        · rcases p3023_3 (m.d 1 3) (by simp) with h3122 | h3122
                          · linarith only [h3122, h9, hlam]
                          · linarith only [h2408, h3122, hlam]
                        · linarith only [h3121, h7, hlam]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h6, hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h2407, hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h2771, hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h3009, hlam, p3023_1]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h7, hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h2408, hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h2772, hlam, p3023_0]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [h2408, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3011_1, p3023_1]
                      · have p3023_0 := h3023c.1
                        have p3023_1 := h3023c.2.1
                        have p3023_2 := h3023c.2.2.1
                        have p3023_3 := h3023c.2.2.2
                        linarith only [hlam, p3023_0]
            · linarith only [h3014, hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            rcases p3011_3 (m.d 0 1) (by simp) with h3137 | h3137
            · rcases p3011_3 (m.d 1 2) (by simp) with h3138 | h3138
              · linarith only [h0, h3138, hlam]
              · rcases p3011_3 (m.d 1 3) (by simp) with h3140 | h3140
                · linarith only [h1, h3140, hlam]
                · linarith only [h2407, h3140, hlam]
            · linarith only [h3137, hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            rcases p3011_3 (m.d 0 1) (by simp) with h3144 | h3144
            · rcases p3011_3 (m.d 1 2) (by simp) with h3145 | h3145
              · linarith only [h0, h3145, hlam]
              · rcases p3011_3 (m.d 1 3) (by simp) with h3147 | h3147
                · linarith only [h1, h3147, hlam]
                · linarith only [h2408, h3147, hlam]
            · linarith only [h3144, hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [h0, hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [h9, hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [h2086, hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [h2336, hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [h1, hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            rcases p3011_3 (m.d 0 1) (by simp) with h3157 | h3157
            · rcases p3011_3 (m.d 1 2) (by simp) with h3158 | h3158
              · linarith only [h3158, h9, hlam]
              · rcases p3011_3 (m.d 1 3) (by simp) with h3160 | h3160
                · rcases p3011_3 (m.d 1 4) (by simp) with h3161 | h3161
                  · linarith only [h2407, h3161, hlam]
                  · linarith only [h2086, h3161, hlam]
                · linarith only [h3160, h9, hlam]
            · linarith only [h0, h3157, hlam]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            rcases p3011_3 (m.d 0 1) (by simp) with h3167 | h3167
            · rcases p3011_3 (m.d 1 2) (by simp) with h3168 | h3168
              · linarith only [h3168, h9, hlam]
              · rcases p3011_3 (m.d 1 3) (by simp) with h3170 | h3170
                · rcases p3011_3 (m.d 1 4) (by simp) with h3171 | h3171
                  · linarith only [h2407, h3171, hlam]
                  · rcases p3011_3 (m.d 1 5) (by simp) with h3173 | h3173
                    · linarith only [h2408, h3173, hlam]
                    · linarith only [h2409, h3173, hlam]
                · linarith only [h2407, h3170, hlam]
            · linarith only [h2, h3167, hlam]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            rcases p3011_3 (m.d 0 1) (by simp) with h3178 | h3178
            · rcases p3011_3 (m.d 1 2) (by simp) with h3179 | h3179
              · linarith only [h3179, h9, hlam]
              · rcases p3011_3 (m.d 1 3) (by simp) with h3181 | h3181
                · rcases p3011_3 (m.d 1 4) (by simp) with h3182 | h3182
                  · linarith only [h2407, h3182, hlam]
                  · rcases p3011_3 (m.d 1 5) (by simp) with h3184 | h3184
                    · linarith only [h2408, h3184, hlam]
                    · rcases h3bigk with h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c | h3186c
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h0, h2086, h2409, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3011_1, p3186_1]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h0, h2086, h2409, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3011_1, p3186_1]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        rcases p3186_3 (m.d 0 3) (by simp) with h3190 | h3190
                        · rcases p3186_3 (m.d 1 3) (by simp) with h3191 | h3191
                          · linarith only [h1, h3191, hlam]
                          · linarith only [h2407, h3191, hlam]
                        · linarith only [h3190, hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        rcases p3186_3 (m.d 0 3) (by simp) with h3195 | h3195
                        · rcases p3186_3 (m.d 1 3) (by simp) with h3196 | h3196
                          · linarith only [h1, h3196, hlam]
                          · linarith only [h2408, h3196, hlam]
                        · linarith only [h3195, hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h1, hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h9, hlam, p3186_1]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        rcases p3186_3 (m.d 0 3) (by simp) with h3203 | h3203
                        · rcases p3186_3 (m.d 1 3) (by simp) with h3204 | h3204
                          · rcases p3186_3 (m.d 2 3) (by simp) with h3205 | h3205
                            · rcases p3186_3 (m.d 3 4) (by simp) with h3206 | h3206
                              · linarith only [h3206, hlam, p3186_0]
                              · rcases p3186_3 (m.d 3 5) (by simp) with h3208 | h3208
                                · linarith only [h2408, h3208, hlam]
                                · linarith only [h3009, h3208, hlam]
                            · linarith only [h2771, h3205, hlam]
                          · linarith only [h3204, hlam, p3186_0]
                        · linarith only [h3203, h6, hlam]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        rcases p3186_3 (m.d 0 3) (by simp) with h3214 | h3214
                        · rcases p3186_3 (m.d 1 3) (by simp) with h3215 | h3215
                          · rcases p3186_3 (m.d 2 3) (by simp) with h3216 | h3216
                            · rcases p3186_3 (m.d 3 4) (by simp) with h3217 | h3217
                              · linarith only [h2407, h3217, hlam]
                              · rcases p3186_3 (m.d 3 5) (by simp) with h3219 | h3219
                                · linarith only [h3219, hlam, p3186_0]
                                · rcases h4bigk with h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c | h3221c
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [hlam, p3221_0]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    rcases p3221_3 (m.d 0 4) (by simp) with h3223 | h3223
                                    · rcases p3221_3 (m.d 1 4) (by simp) with h3224 | h3224
                                      · linarith only [h2, h3224, hlam]
                                      · rcases p3221_3 (m.d 2 4) (by simp) with h3226 | h3226
                                        · linarith only [h3226, h5, hlam]
                                        · linarith only [h2086, h3226, hlam]
                                    · linarith only [h2, h3223, hlam]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    rcases p3221_3 (m.d 0 4) (by simp) with h3230 | h3230
                                    · rcases p3221_3 (m.d 1 4) (by simp) with h3231 | h3231
                                      · linarith only [h2, h3231, hlam]
                                      · rcases p3221_3 (m.d 2 4) (by simp) with h3233 | h3233
                                        · linarith only [h3233, h5, hlam]
                                        · rcases p3221_3 (m.d 3 4) (by simp) with h3235 | h3235
                                          · linarith only [h3235, h6, hlam]
                                          · rcases p3221_3 (m.d 4 5) (by simp) with h3237 | h3237
                                            · linarith only [h3237, h8, hlam]
                                            · linarith only [h2773, h3237, hlam]
                                    · linarith only [h3230, h5, hlam]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    rcases p3221_3 (m.d 0 4) (by simp) with h3241 | h3241
                                    · rcases p3221_3 (m.d 1 4) (by simp) with h3242 | h3242
                                      · linarith only [h2, h3242, hlam]
                                      · linarith only [h2407, h3242, hlam]
                                    · linarith only [h3241, h6, hlam]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h2086, h2773, h6, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3221_1]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h2, hlam, p3221_1]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [hlam, p3221_0]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h2086, hlam, p3221_0]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h0, h2409, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3011_1, p3221_1]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h2409, hlam, p3221_0]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h5, hlam, p3221_1]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h2773, hc14, hc45, hlam, hphi, p3221_1]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [hlam, p3221_0]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h0, h2773, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3221_1]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h2773, hlam, p3221_0]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h6, hlam, p3221_1]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h2407, hlam, p3221_0]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h2771, hlam, p3221_0]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [hlam, p3221_0]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h3009, hlam, p3221_0]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h8, hlam, p3221_0]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    rcases p3221_3 (m.d 0 4) (by simp) with h3263 | h3263
                                    · rcases p3221_3 (m.d 1 4) (by simp) with h3264 | h3264
                                      · linarith only [h3264, hlam, p3221_0]
                                      · rcases p3221_3 (m.d 2 4) (by simp) with h3266 | h3266
                                        · linarith only [h2773, h3266, hlam]
                                        · linarith only [h2086, h3266, hlam]
                                    · linarith only [h2, h3263, hlam]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [h0, h2086, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3221_1]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    rcases p3221_3 (m.d 0 4) (by simp) with h3271 | h3271
                                    · rcases p3221_3 (m.d 1 4) (by simp) with h3272 | h3272
                                      · linarith only [h2409, h3272, hlam]
                                      · linarith only [h2407, h3272, hlam]
                                    · linarith only [h3271, h6, hlam]
                                  · have p3221_0 := h3221c.1
                                    have p3221_1 := h3221c.2.1
                                    have p3221_2 := h3221c.2.2.1
                                    have p3221_3 := h3221c.2.2.2
                                    linarith only [hlam, p3221_0]
                            · linarith only [h2772, h3216, hlam]
                          · linarith only [h3215, hlam, p3186_0]
                        · linarith only [h3214, h7, hlam]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h4, hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p3011_1, p3186_1]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        rcases p3186_3 (m.d 0 3) (by simp) with h3283 | h3283
                        · rcases p3186_3 (m.d 1 3) (by simp) with h3284 | h3284
                          · linarith only [h3284, h9, hlam]
                          · linarith only [h2407, h3284, hlam]
                        · linarith only [h3283, h6, hlam]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        rcases p3186_3 (m.d 0 3) (by simp) with h3288 | h3288
                        · rcases p3186_3 (m.d 1 3) (by simp) with h3289 | h3289
                          · linarith only [h3289, h9, hlam]
                          · linarith only [h2408, h3289, hlam]
                        · linarith only [h3288, h7, hlam]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h6, hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h2407, hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h2771, hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h3009, hlam, p3186_1]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h7, hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h2408, hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h2772, hlam, p3186_0]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [h1, h2408, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3186_1]
                      · have p3186_0 := h3186c.1
                        have p3186_1 := h3186c.2.1
                        have p3186_2 := h3186c.2.2.1
                        have p3186_3 := h3186c.2.2.2
                        linarith only [hlam, p3186_0]
                · linarith only [h2408, h3181, hlam]
            · linarith only [h3, h3178, hlam]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [h2, hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [h0, h2409, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3011_1]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [h2407, hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [h2409, hlam, p3011_1]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [h3, hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            rcases p3011_3 (m.d 0 1) (by simp) with h3311 | h3311
            · rcases p3011_3 (m.d 1 2) (by simp) with h3312 | h3312
              · linarith only [h2336, h3312, hlam]
              · rcases p3011_3 (m.d 1 3) (by simp) with h3314 | h3314
                · rcases p3011_3 (m.d 1 4) (by simp) with h3315 | h3315
                  · linarith only [h2409, h3315, hlam]
                  · linarith only [h2086, h3315, hlam]
                · linarith only [h3314, h9, hlam]
            · linarith only [h0, h3311, hlam]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [h2408, hlam, p3011_0]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            rcases p3011_3 (m.d 0 1) (by simp) with h3321 | h3321
            · rcases p3011_3 (m.d 1 2) (by simp) with h3322 | h3322
              · linarith only [h2336, h3322, hlam]
              · rcases p3011_3 (m.d 1 3) (by simp) with h3324 | h3324
                · rcases p3011_3 (m.d 1 4) (by simp) with h3325 | h3325
                  · linarith only [h2409, h3325, hlam]
                  · rcases p3011_3 (m.d 1 5) (by simp) with h3327 | h3327
                    · rcases h3bigk with h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c | h3328c
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h0, h2086, h2408, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3011_1, p3328_1]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h0, h2086, h2408, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3011_1, p3328_1]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h2336, h2407, h2773, h6, h8, hlam, p3011_1, p3328_2]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        rcases p3328_3 (m.d 0 3) (by simp) with h3333 | h3333
                        · rcases p3328_3 (m.d 1 3) (by simp) with h3334 | h3334
                          · linarith only [h1, h3334, hlam]
                          · linarith only [h2408, h3334, hlam]
                        · linarith only [h3333, hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h1, hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h9, hlam, p3328_1]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        rcases p3328_3 (m.d 0 3) (by simp) with h3341 | h3341
                        · rcases p3328_3 (m.d 1 3) (by simp) with h3342 | h3342
                          · rcases p3328_3 (m.d 2 3) (by simp) with h3343 | h3343
                            · rcases p3328_3 (m.d 3 4) (by simp) with h3344 | h3344
                              · linarith only [h3344, hlam, p3328_0]
                              · rcases p3328_3 (m.d 3 5) (by simp) with h3346 | h3346
                                · linarith only [h2408, h3346, hlam]
                                · linarith only [h3009, h3346, hlam]
                            · linarith only [h2771, h3343, hlam]
                          · linarith only [h3342, hlam, p3328_0]
                        · linarith only [h3341, h6, hlam]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        rcases p3328_3 (m.d 0 3) (by simp) with h3352 | h3352
                        · rcases p3328_3 (m.d 1 3) (by simp) with h3353 | h3353
                          · rcases p3328_3 (m.d 2 3) (by simp) with h3354 | h3354
                            · rcases p3328_3 (m.d 3 4) (by simp) with h3355 | h3355
                              · linarith only [h2407, h3355, hlam]
                              · rcases p3328_3 (m.d 3 5) (by simp) with h3357 | h3357
                                · linarith only [h3357, hlam, p3328_0]
                                · rcases h4bigk with h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c | h3359c
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [hlam, p3359_0]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h2336, h2773, h8, hlam, p3011_1, p3359_2]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    rcases p3359_3 (m.d 0 4) (by simp) with h3362 | h3362
                                    · rcases p3359_3 (m.d 1 4) (by simp) with h3363 | h3363
                                      · linarith only [h2, h3363, hlam]
                                      · rcases p3359_3 (m.d 2 4) (by simp) with h3365 | h3365
                                        · linarith only [h3365, h5, hlam]
                                        · rcases p3359_3 (m.d 3 4) (by simp) with h3367 | h3367
                                          · linarith only [h3367, h6, hlam]
                                          · rcases p3359_3 (m.d 4 5) (by simp) with h3369 | h3369
                                            · linarith only [h3369, h8, hlam]
                                            · linarith only [h2773, h3369, hlam]
                                    · linarith only [h3362, h5, hlam]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h2336, h2407, h2773, h8, hlam, p3011_1, p3359_2]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h0, h2336, h2773, h4, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3011_1, p3359_1]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h2, hlam, p3359_1]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [hlam, p3359_0]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h2086, hlam, p3359_0]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h2408, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3011_1, p3359_1]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h2409, hlam, p3359_0]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h5, hlam, p3359_1]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h0, h2773, h4, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3359_1]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [hlam, p3359_0]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h0, h2773, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3359_1]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h2773, hlam, p3359_0]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h6, hlam, p3359_1]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h2407, hlam, p3359_0]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h2771, hlam, p3359_0]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [hlam, p3359_0]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h3009, hlam, p3359_0]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h8, hlam, p3359_0]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    rcases p3359_3 (m.d 0 4) (by simp) with h3391 | h3391
                                    · rcases p3359_3 (m.d 1 4) (by simp) with h3392 | h3392
                                      · linarith only [h3392, hlam, p3359_0]
                                      · rcases p3359_3 (m.d 2 4) (by simp) with h3394 | h3394
                                        · linarith only [h2773, h3394, hlam]
                                        · linarith only [h2086, h3394, hlam]
                                    · linarith only [h2, h3391, hlam]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [h0, h2086, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3359_1]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    rcases p3359_3 (m.d 0 4) (by simp) with h3399 | h3399
                                    · rcases p3359_3 (m.d 1 4) (by simp) with h3400 | h3400
                                      · linarith only [h2409, h3400, hlam]
                                      · linarith only [h2407, h3400, hlam]
                                    · linarith only [h3399, h6, hlam]
                                  · have p3359_0 := h3359c.1
                                    have p3359_1 := h3359c.2.1
                                    have p3359_2 := h3359c.2.2.1
                                    have p3359_3 := h3359c.2.2.2
                                    linarith only [hlam, p3359_0]
                            · linarith only [h2772, h3354, hlam]
                          · linarith only [h3353, hlam, p3328_0]
                        · linarith only [h3352, h7, hlam]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h4, hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h0, h2407, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3328_1]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        rcases p3328_3 (m.d 0 3) (by simp) with h3411 | h3411
                        · rcases p3328_3 (m.d 1 3) (by simp) with h3412 | h3412
                          · linarith only [h3412, h9, hlam]
                          · linarith only [h2407, h3412, hlam]
                        · linarith only [h3411, h6, hlam]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        rcases p3328_3 (m.d 0 3) (by simp) with h3416 | h3416
                        · rcases p3328_3 (m.d 1 3) (by simp) with h3417 | h3417
                          · linarith only [h3417, h9, hlam]
                          · linarith only [h2408, h3417, hlam]
                        · linarith only [h3416, h7, hlam]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h6, hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h2407, hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h2771, hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h3009, hlam, p3328_1]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h7, hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h2408, hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h2772, hlam, p3328_0]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [h1, h2408, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3328_1]
                      · have p3328_0 := h3328c.1
                        have p3328_1 := h3328c.2.1
                        have p3328_2 := h3328c.2.2.1
                        have p3328_3 := h3328c.2.2.2
                        linarith only [hlam, p3328_0]
                    · linarith only [h2409, h3327, hlam]
                · linarith only [h2407, h3324, hlam]
            · linarith only [h2, h3321, hlam]
          · have p3011_0 := h3011c.1
            have p3011_1 := h3011c.2.1
            have p3011_2 := h3011c.2.2.1
            have p3011_3 := h3011c.2.2.2
            linarith only [hlam, p3011_0]
    · linarith only [h2408, h2772, h9, hlam]
  · linarith only [h2407, h2771, h9, hlam]

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2086 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2336 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2407 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2408 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 4 5 (by decide) (by decide) with h2409 | h2409
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2086 h2336 h2407 h2408 h2409
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2086 h2336 h2407 h2408 h2409

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2086 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2336 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2407 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2408 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 4 5 (by decide) (by decide) with h3437 | h3437
  · linarith only [h2407, h2408, h3437, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h3439 | h3439
    · rcases m.htr 2 3 5 (by decide) (by decide) with h3440 | h3440
      · linarith only [h0, h2407, h2408, h3440, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3442 | h3442
        · linarith only [h0, h3437, h3439, h3440, h3442, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h3444 | h3444
          · linarith only [h2086, h2407, h3442, h3444, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
          · rcases h1bigk with h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c | h3446c
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h0, h2086, h3439, h3440, h3444, h4, h6, h8, hlam, p3446_2]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              rcases p3446_3 (m.d 0 1) (by simp) with h3449 | h3449
              · rcases p3446_3 (m.d 1 2) (by simp) with h3450 | h3450
                · linarith only [h0, h3450, hlam]
                · rcases p3446_3 (m.d 1 3) (by simp) with h3452 | h3452
                  · linarith only [h3452, hlam, p3446_0]
                  · rcases p3446_3 (m.d 1 4) (by simp) with h3454 | h3454
                    · linarith only [h2, h3454, hlam]
                    · rcases p3446_3 (m.d 1 5) (by simp) with h3456 | h3456
                      · linarith only [h3, h3456, hlam]
                      · linarith only [h2408, h3456, hlam]
              · linarith only [h3449, hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              rcases p3446_3 (m.d 0 1) (by simp) with h3460 | h3460
              · rcases p3446_3 (m.d 1 2) (by simp) with h3461 | h3461
                · linarith only [h0, h3461, hlam]
                · rcases p3446_3 (m.d 1 3) (by simp) with h3463 | h3463
                  · linarith only [h1, h3463, hlam]
                  · linarith only [h2407, h3463, hlam]
              · linarith only [h3460, hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              rcases p3446_3 (m.d 0 1) (by simp) with h3467 | h3467
              · rcases p3446_3 (m.d 1 2) (by simp) with h3468 | h3468
                · linarith only [h0, h3468, hlam]
                · rcases p3446_3 (m.d 1 3) (by simp) with h3470 | h3470
                  · linarith only [h1, h3470, hlam]
                  · rcases p3446_3 (m.d 1 4) (by simp) with h3472 | h3472
                    · linarith only [h2, h3472, hlam]
                    · rcases p3446_3 (m.d 1 5) (by simp) with h3474 | h3474
                      · linarith only [h3474, hlam, p3446_0]
                      · rcases h3bigk with h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c | h3476c
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [hlam, p3476_0]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          rcases p3476_3 (m.d 0 3) (by simp) with h3478 | h3478
                          · rcases p3476_3 (m.d 1 3) (by simp) with h3479 | h3479
                            · linarith only [h1, h3479, hlam]
                            · rcases p3476_3 (m.d 2 3) (by simp) with h3481 | h3481
                              · linarith only [h3481, h4, hlam]
                              · linarith only [h3481, h9, hlam]
                          · linarith only [h1, h3478, hlam]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          rcases p3476_3 (m.d 0 3) (by simp) with h3485 | h3485
                          · rcases p3476_3 (m.d 1 3) (by simp) with h3486 | h3486
                            · linarith only [h1, h3486, hlam]
                            · rcases p3476_3 (m.d 2 3) (by simp) with h3488 | h3488
                              · linarith only [h3488, h4, hlam]
                              · rcases p3476_3 (m.d 3 4) (by simp) with h3490 | h3490
                                · linarith only [h3490, h6, hlam]
                                · rcases p3476_3 (m.d 3 5) (by simp) with h3492 | h3492
                                  · linarith only [h3492, h7, hlam]
                                  · linarith only [h3440, h3492, hlam]
                          · linarith only [h3485, h4, hlam]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h2407, h3440, h3444, h6, h8, h9, hlam, p3476_2]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h0, h2086, h3439, h3440, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3476_1]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h1, hlam, p3476_0]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [hlam, p3476_0]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h9, hlam, p3476_1]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h3440, h3444, h8, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p3476_1]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h2408, hlam, p3476_0]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h4, hlam, p3476_0]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h3440, h3444, h8, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3476_1]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [hlam, p3476_0]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h0, h3440, h3444, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3476_1]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h3440, hlam, p3476_0]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h6, hlam, p3476_0]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h2407, hlam, p3476_0]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h3439, hlam, p3476_0]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [hlam, p3476_0]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h3444, hlam, p3476_1]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h7, hlam, p3476_0]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h0, h2407, h3444, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3476_1]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [h0, h2086, h3439, h3444, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3476_1]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          rcases p3476_3 (m.d 0 3) (by simp) with h3516 | h3516
                          · rcases p3476_3 (m.d 1 3) (by simp) with h3517 | h3517
                            · linarith only [h2408, h3517, hlam]
                            · linarith only [h2407, h3517, hlam]
                          · linarith only [h3516, h6, hlam]
                        · have p3476_0 := h3476c.1
                          have p3476_1 := h3476c.2.1
                          have p3476_2 := h3476c.2.2.1
                          have p3476_3 := h3476c.2.2.2
                          linarith only [hlam, p3476_0]
              · linarith only [h3467, hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h0, hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h9, hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h2086, hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h2336, hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h1, hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h0, h2408, h3444, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3446_1]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h0, h2086, h2408, h3444, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3446_1]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h2408, hlam, p3446_1]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h2, hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h0, h2407, h2408, h3444, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3446_1]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h2407, hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h3437, hlam, p3446_1]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h3, hlam, p3446_0]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              rcases p3446_3 (m.d 0 1) (by simp) with h3539 | h3539
              · rcases p3446_3 (m.d 1 2) (by simp) with h3540 | h3540
                · linarith only [h2336, h3540, hlam]
                · rcases p3446_3 (m.d 1 3) (by simp) with h3542 | h3542
                  · linarith only [h2408, h3542, hlam]
                  · linarith only [h3542, h9, hlam]
              · linarith only [h0, h3539, hlam]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [h0, h2336, h2407, h3440, h3444, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3446_1]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              rcases p3446_3 (m.d 0 1) (by simp) with h3547 | h3547
              · rcases p3446_3 (m.d 1 2) (by simp) with h3548 | h3548
                · linarith only [h2336, h3548, hlam]
                · rcases p3446_3 (m.d 1 3) (by simp) with h3550 | h3550
                  · linarith only [h2408, h3550, hlam]
                  · linarith only [h2407, h3550, hlam]
              · linarith only [h2, h3547, hlam]
            · have p3446_0 := h3446c.1
              have p3446_1 := h3446c.2.1
              have p3446_2 := h3446c.2.2.1
              have p3446_3 := h3446c.2.2.2
              linarith only [hlam, p3446_0]
    · linarith only [h1, h2407, h3439, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2086 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2336 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2407 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 5 (by decide) (by decide) with h2408 | h2408
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2086 h2336 h2407 h2408
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2086 h2336 h2407 h2408

end R2N4
