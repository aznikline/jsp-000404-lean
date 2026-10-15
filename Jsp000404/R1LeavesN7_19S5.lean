import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8564000 in
set_option maxHeartbeats 8564000 in
theorem r1l7_21_14_H_I_L_I_s3_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h2783 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h2784 | h2784
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2785 | h2785
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2786 | h2786
      · linarith only [h0, h2786, h4, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2788 | h2788
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2789 | h2789
          · linarith only [h2785, h2786, h2789, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2791 | h2791
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2792 | h2792
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2793 | h2793
                · linarith only [h0, h2785, h2789, h2791, h2793, hc02, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h2783, h2793, h4, hlam]
              · linarith only [h2785, h2786, h2791, h2792, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2797 | h2797
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2798 | h2798
                · linarith only [h2785, h2786, h2789, h2798, hlam]
                · linarith only [h2783, h2798, h4, hlam]
              · linarith only [h2786, h2788, h2797, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2802 | h2802
          · linarith only [h2785, h2786, h2802, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2804 | h2804
            · linarith only [h2785, h2788, h2804, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2806 | h2806
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2807 | h2807
                · linarith only [h2785, h2788, h2802, h2807, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h2783, h2807, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2810 | h2810
                · linarith only [h2785, h2786, h2802, h2810, hlam]
                · linarith only [h2784, h2785, h2786, h2806, h2810, h4, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2813 | h2813
      · linarith only [h2785, h2813, h4, hc02, hc23, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2815 | h2815
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2816 | h2816
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2817 | h2817
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2818 | h2818
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2819 | h2819
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2820 | h2820
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2821 | h2821
                    · rcases h1bigk with h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c | h2822c
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [hlam, p2822_0]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h2815, hc01, hc25, hlam, hphi, ht0b, ht5b, p2822_1]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h2816, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2822_1]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h2813, h2815, hc01, hc25, hlam, hphi, ht0b, ht5b, p2822_1]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        rcases p2822_3 (m.d 0 1) (by simp) with h2827 | h2827
                        · rcases p2822_3 (m.d 1 2) (by simp) with h2828 | h2828
                          · linarith only [h0, h2828, hlam]
                          · linarith only [h2815, h2828, hlam]
                        · linarith only [h2827, hlam, p2822_0]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h0, hlam, p2822_0]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [hlam, p2822_0]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h2785, hlam, p2822_1]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h2813, hlam, p2822_1]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h0, h2815, h2820, hc01, hc45, hlam, hphi, ht0b, ht5b, p2822_1]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h1, hlam, p2822_0]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2822_1]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [hlam, p2822_0]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h1, h2813, h2815, h2820, hc01, hc45, hlam, hphi, ht0b, ht5b, p2822_1]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h1, h2815, h2820, hc01, hc45, hlam, hphi, ht0b, ht5b, p2822_1]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h2, hlam, p2822_0]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h2815, h2820, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2822_1]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h2816, hlam, p2822_1]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [hlam, p2822_0]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h1, h2815, h2816, h2820, hc01, hc45, hlam, hphi, ht0b, ht5b, p2822_1]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h3, hlam, p2822_0]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h2815, hlam, p2822_0]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h2817, hlam, p2822_0]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [h2818, hlam, p2822_0]
                      · have p2822_0 := h2822c.1
                        have p2822_1 := h2822c.2.1
                        have p2822_2 := h2822c.2.2.1
                        have p2822_3 := h2822c.2.2.2
                        linarith only [hlam, p2822_0]
                    · rcases h1bigk with h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [hlam, p2852_0]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h2815, h2820, h2821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h2785, h2815, h2820, h2821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h2813, h2815, h2820, h2821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h2815, h2820, h2821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h0, hlam, p2852_0]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [hlam, p2852_0]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h2785, hlam, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h2813, hlam, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h0, h2815, h2819, h2820, h2821, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h1, hlam, p2852_0]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [hlam, p2852_0]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h1, h2813, h2815, h2820, h2821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h1, h2815, h2820, h2821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h2, hlam, p2852_0]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h2815, h2820, h2821, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h2816, hlam, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [hlam, p2852_0]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h1, h2815, h2816, h2820, h2821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2852_1]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h3, hlam, p2852_0]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h2815, hlam, p2852_0]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h2817, hlam, p2852_0]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [h2818, hlam, p2852_0]
                      · have p2852_0 := h2852c.1
                        have p2852_1 := h2852c.2.1
                        have p2852_2 := h2852c.2.2.1
                        have p2852_3 := h2852c.2.2.2
                        linarith only [hlam, p2852_0]
                  · linarith only [h2784, h2820, h4, hlam]
                · linarith only [h1, h2783, h2785, h2815, h2819, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h2813, h2815, h2818, hlam]
            · linarith only [h2785, h2815, h2817, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2882 | h2882
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2883 | h2883
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2884 | h2884
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2885 | h2885
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2886 | h2886
                    · rcases h1bigk with h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2815, hc01, hc25, hlam, hphi, ht0b, ht5b, p2887_1]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2785, h2815, h2885, hc01, hc45, hlam, hphi, ht0b, ht5b, p2887_1]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2813, h2815, h2885, hc01, hc45, hlam, hphi, ht0b, ht5b, p2887_1]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        rcases p2887_3 (m.d 0 1) (by simp) with h2892 | h2892
                        · rcases p2887_3 (m.d 1 2) (by simp) with h2893 | h2893
                          · linarith only [h0, h2893, hlam]
                          · linarith only [h2815, h2893, hlam]
                        · linarith only [h2892, hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h0, hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2785, hlam, p2887_1]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2813, hlam, p2887_1]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2887_1]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h1, hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2887_1]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2816, hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2815, h2816, h2884, h2885, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2887_1]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2, hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2815, h2816, h2884, h2885, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2887_1]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2816, h2884, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2887_1]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2815, h2816, h2884, h2885, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2887_1]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h3, hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2815, hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2882, hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [h2883, hlam, p2887_0]
                      · have p2887_0 := h2887c.1
                        have p2887_1 := h2887c.2.1
                        have p2887_2 := h2887c.2.2.1
                        have p2887_3 := h2887c.2.2.2
                        linarith only [hlam, p2887_0]
                    · linarith only [h2813, h2815, h2816, h2885, h2886, hlam]
                  · linarith only [h2783, h2785, h2815, h2816, h2883, h2885, h4, hc02, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h1, h2783, h2785, h2815, h2884, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h2785, h2815, h2816, h2883, hlam]
            · linarith only [h2785, h2815, h2882, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2922 | h2922
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2923 | h2923
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2924 | h2924
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2925 | h2925
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2926 | h2926
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2927 | h2927
                    · rcases h1bigk with h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c | h2928c
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [hlam, p2928_0]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        rcases p2928_3 (m.d 0 1) (by simp) with h2930 | h2930
                        · rcases p2928_3 (m.d 1 2) (by simp) with h2931 | h2931
                          · linarith only [h2931, hlam, p2928_0]
                          · rcases p2928_3 (m.d 1 3) (by simp) with h2933 | h2933
                            · linarith only [h1, h2933, hlam]
                            · linarith only [h2785, h2933, hlam]
                        · linarith only [h2930, hlam, p2928_0]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h2922, h2927, hc01, hc45, hlam, hphi, ht0b, ht5b, p2928_1]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h2922, h2927, hc01, hc45, hlam, hphi, ht0b, ht5b, p2928_1]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        rcases p2928_3 (m.d 0 1) (by simp) with h2939 | h2939
                        · rcases p2928_3 (m.d 1 2) (by simp) with h2940 | h2940
                          · linarith only [h0, h2940, hlam]
                          · rcases p2928_3 (m.d 1 3) (by simp) with h2942 | h2942
                            · linarith only [h1, h2942, hlam]
                            · linarith only [h2923, h2942, hlam]
                        · linarith only [h2939, hlam, p2928_0]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h0, hlam, p2928_0]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [hlam, p2928_0]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h2785, hlam, p2928_1]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h2813, hlam, p2928_1]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h2815, hlam, p2928_1]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h1, hlam, p2928_0]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2928_1]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [hlam, p2928_0]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h1, h2922, h2927, hc01, hc45, hlam, hphi, ht0b, ht5b, p2928_1]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p2928_1]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h2, hlam, p2928_0]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2928_1]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h2922, hlam, p2928_1]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [hlam, p2928_0]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h1, h2815, h2922, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2928_1]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h3, hlam, p2928_0]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2928_1]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h2923, hlam, p2928_0]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [h2924, hlam, p2928_0]
                      · have p2928_0 := h2928c.1
                        have p2928_1 := h2928c.2.1
                        have p2928_2 := h2928c.2.2.1
                        have p2928_3 := h2928c.2.2.2
                        linarith only [hlam, p2928_0]
                    · rcases h1bigk with h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c | h2966c
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [hlam, p2966_0]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        rcases p2966_3 (m.d 0 1) (by simp) with h2968 | h2968
                        · rcases p2966_3 (m.d 1 2) (by simp) with h2969 | h2969
                          · linarith only [h2969, hlam, p2966_0]
                          · rcases p2966_3 (m.d 1 3) (by simp) with h2971 | h2971
                            · linarith only [h1, h2971, hlam]
                            · linarith only [h2785, h2971, hlam]
                        · linarith only [h2968, hlam, p2966_0]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h2922, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h2924, h2927, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h2924, h2927, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h0, hlam, p2966_0]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [hlam, p2966_0]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h2785, hlam, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h2813, hlam, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h2815, hlam, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h1, hlam, p2966_0]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [hlam, p2966_0]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h1, h2924, h2927, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h2, hlam, p2966_0]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h2922, hlam, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [hlam, p2966_0]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h1, h2815, h2922, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h3, hlam, p2966_0]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2966_1]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h2923, hlam, p2966_0]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [h2924, hlam, p2966_0]
                      · have p2966_0 := h2966c.1
                        have p2966_1 := h2966c.2.1
                        have p2966_2 := h2966c.2.2.1
                        have p2966_3 := h2966c.2.2.2
                        linarith only [hlam, p2966_0]
                  · linarith only [h2784, h2926, h4, hlam]
                · linarith only [h2785, h2922, h2925, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3000 | h3000
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3001 | h3001
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3002 | h3002
                    · linarith only [h2922, h2924, h3002, hlam]
                    · rcases h1bigk with h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [hlam, p3004_0]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        rcases p3004_3 (m.d 0 1) (by simp) with h3006 | h3006
                        · rcases p3004_3 (m.d 1 2) (by simp) with h3007 | h3007
                          · linarith only [h3007, hlam, p3004_0]
                          · rcases p3004_3 (m.d 1 3) (by simp) with h3009 | h3009
                            · linarith only [h1, h3009, hlam]
                            · linarith only [h2785, h3009, hlam]
                        · linarith only [h3006, hlam, p3004_0]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h2922, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3004_1]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        rcases p3004_3 (m.d 0 1) (by simp) with h3014 | h3014
                        · rcases p3004_3 (m.d 1 2) (by simp) with h3015 | h3015
                          · linarith only [h0, h3015, hlam]
                          · rcases p3004_3 (m.d 1 3) (by simp) with h3017 | h3017
                            · linarith only [h1, h3017, hlam]
                            · linarith only [h2922, h3017, hlam]
                        · linarith only [h3014, hlam, p3004_0]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        rcases p3004_3 (m.d 0 1) (by simp) with h3021 | h3021
                        · rcases p3004_3 (m.d 1 2) (by simp) with h3022 | h3022
                          · linarith only [h0, h3022, hlam]
                          · rcases p3004_3 (m.d 1 3) (by simp) with h3024 | h3024
                            · linarith only [h1, h3024, hlam]
                            · linarith only [h2923, h3024, hlam]
                        · linarith only [h3021, hlam, p3004_0]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h0, hlam, p3004_0]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [hlam, p3004_0]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h2785, hlam, p3004_1]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h2813, hlam, p3004_1]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h2815, hlam, p3004_1]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h1, hlam, p3004_0]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3004_1]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [hlam, p3004_0]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3004_1]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p3004_1]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h2, hlam, p3004_0]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3004_1]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h2922, hlam, p3004_1]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [hlam, p3004_0]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h2924, hlam, p3004_1]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h3, hlam, p3004_0]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3004_1]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h2923, hlam, p3004_0]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [h2784, h2924, h3000, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3004_1]
                      · have p3004_0 := h3004c.1
                        have p3004_1 := h3004c.2.1
                        have p3004_2 := h3004c.2.2.1
                        have p3004_3 := h3004c.2.2.2
                        linarith only [hlam, p3004_0]
                  · linarith only [h2784, h3001, h4, hlam]
                · linarith only [h2785, h2922, h3000, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3050 | h3050
              · linarith only [h2922, h2923, h3050, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3052 | h3052
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3053 | h3053
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3054 | h3054
                    · linarith only [h2922, h2923, h3050, h3054, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · rcases h1bigk with h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [hlam, p3056_0]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        rcases p3056_3 (m.d 0 1) (by simp) with h3058 | h3058
                        · rcases p3056_3 (m.d 1 2) (by simp) with h3059 | h3059
                          · linarith only [h3059, hlam, p3056_0]
                          · rcases p3056_3 (m.d 1 3) (by simp) with h3061 | h3061
                            · linarith only [h1, h3061, hlam]
                            · linarith only [h2785, h3061, hlam]
                        · linarith only [h3058, hlam, p3056_0]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2922, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        rcases p3056_3 (m.d 0 1) (by simp) with h3066 | h3066
                        · rcases p3056_3 (m.d 1 2) (by simp) with h3067 | h3067
                          · linarith only [h0, h3067, hlam]
                          · rcases p3056_3 (m.d 1 3) (by simp) with h3069 | h3069
                            · linarith only [h1, h3069, hlam]
                            · linarith only [h2922, h3069, hlam]
                        · linarith only [h3066, hlam, p3056_0]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2922, h2923, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h0, hlam, p3056_0]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [hlam, p3056_0]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2785, hlam, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2813, hlam, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2815, hlam, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h1, hlam, p3056_0]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2784, h2923, h3054, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [hlam, p3056_0]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2784, h2923, h3052, h3054, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2923, hlam, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2, hlam, p3056_0]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2922, hlam, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [hlam, p3056_0]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h3050, hlam, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h3, hlam, p3056_0]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2784, h2922, h2923, h3, h3052, h3054, h4, hc01, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2784, h2922, h2923, h3052, h3054, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [h2784, h2923, h3052, h3054, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3056_1]
                      · have p3056_0 := h3056c.1
                        have p3056_1 := h3056c.2.1
                        have p3056_2 := h3056c.2.2.1
                        have p3056_3 := h3056c.2.2.2
                        linarith only [hlam, p3056_0]
                  · linarith only [h2784, h3053, h4, hlam]
                · linarith only [h1, h2785, h2922, h3052, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3096 | h3096
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3097 | h3097
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3098 | h3098
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3099 | h3099
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3100 | h3100
                    · rcases h1bigk with h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        rcases p3101_3 (m.d 0 1) (by simp) with h3103 | h3103
                        · rcases p3101_3 (m.d 1 2) (by simp) with h3104 | h3104
                          · linarith only [h3104, hlam, p3101_0]
                          · rcases p3101_3 (m.d 1 3) (by simp) with h3106 | h3106
                            · linarith only [h1, h3106, hlam]
                            · linarith only [h2785, h3106, hlam]
                        · linarith only [h3103, hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h3096, hc01, hc35, hlam, hphi, ht0b, ht5b, p3101_1]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h2922, h3096, h3100, hc01, hc45, hlam, hphi, ht0b, ht5b, p3101_1]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        rcases p3101_3 (m.d 0 1) (by simp) with h3112 | h3112
                        · rcases p3101_3 (m.d 1 2) (by simp) with h3113 | h3113
                          · linarith only [h0, h3113, hlam]
                          · rcases p3101_3 (m.d 1 3) (by simp) with h3115 | h3115
                            · linarith only [h1, h3115, hlam]
                            · linarith only [h3096, h3115, hlam]
                        · linarith only [h3112, hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h0, hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h2785, hlam, p3101_1]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h2813, hlam, p3101_1]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h2815, hlam, p3101_1]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h1, hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3101_1]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h2922, hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h2922, h3098, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3101_1]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h2, hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h2922, h3098, hc12, hc23, hlam, hphi, p3101_1]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h2922, h3098, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3101_1]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h2815, h2922, h3098, hc12, hc23, hlam, hphi, p3101_1]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h3, hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3101_1]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h3096, hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [h3097, hlam, p3101_0]
                      · have p3101_0 := h3101c.1
                        have p3101_1 := h3101c.2.1
                        have p3101_2 := h3101c.2.2.1
                        have p3101_3 := h3101c.2.2.2
                        linarith only [hlam, p3101_0]
                    · linarith only [h2784, h2785, h2922, h3098, h3100, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h2784, h3, h3097, h3099, h4, hlam]
                · linarith only [h2783, h3098, h4, hlam]
              · linarith only [h2922, h3096, h3097, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3143 | h3143
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3144 | h3144
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3145 | h3145
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3146 | h3146
                    · rcases h1bigk with h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c | h3147c
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        rcases p3147_3 (m.d 0 1) (by simp) with h3149 | h3149
                        · rcases p3147_3 (m.d 1 2) (by simp) with h3150 | h3150
                          · linarith only [h3150, hlam, p3147_0]
                          · rcases p3147_3 (m.d 1 3) (by simp) with h3152 | h3152
                            · linarith only [h1, h3152, hlam]
                            · linarith only [h2785, h3152, hlam]
                        · linarith only [h3149, hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        rcases p3147_3 (m.d 0 1) (by simp) with h3156 | h3156
                        · rcases p3147_3 (m.d 1 2) (by simp) with h3157 | h3157
                          · linarith only [h0, h3157, hlam]
                          · rcases p3147_3 (m.d 1 3) (by simp) with h3159 | h3159
                            · linarith only [h3159, hlam, p3147_0]
                            · rcases p3147_3 (m.d 1 4) (by simp) with h3161 | h3161
                              · linarith only [h2, h3161, hlam]
                              · linarith only [h2922, h3161, hlam]
                        · linarith only [h3156, hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h3143, hc01, hc45, hlam, hphi, ht0b, ht5b, p3147_1]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        rcases p3147_3 (m.d 0 1) (by simp) with h3166 | h3166
                        · rcases p3147_3 (m.d 1 2) (by simp) with h3167 | h3167
                          · linarith only [h0, h3167, hlam]
                          · rcases p3147_3 (m.d 1 3) (by simp) with h3169 | h3169
                            · linarith only [h1, h3169, hlam]
                            · rcases p3147_3 (m.d 1 4) (by simp) with h3171 | h3171
                              · linarith only [h2, h3171, hlam]
                              · linarith only [h3143, h3171, hlam]
                        · linarith only [h3166, hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h0, hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h2785, hlam, p3147_1]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h2813, hlam, p3147_1]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h2815, hlam, p3147_1]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h1, hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h3096, hc12, hc35, hlam, hphi, ht23, p3147_1]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h2922, hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h3096, hlam, p3147_1]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h2, hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3147_1]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h1, h2783, h2922, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3147_1]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h1, h2783, h2785, h2922, h3096, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3147_1]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h3, hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3147_1]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h2785, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3147_1]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [h3143, hlam, p3147_0]
                      · have p3147_0 := h3147c.1
                        have p3147_1 := h3147c.2.1
                        have p3147_2 := h3147c.2.2.1
                        have p3147_3 := h3147c.2.2.2
                        linarith only [hlam, p3147_0]
                    · linarith only [h2784, h2785, h2922, h3144, h3146, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h2, h3143, h3145, h4, hlam]
                · linarith only [h2783, h3144, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3198 | h3198
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3199 | h3199
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3200 | h3200
                    · linarith only [h2785, h2922, h3143, h3198, h3200, hc12, hc23, hlam, hphi]
                    · linarith only [h2784, h2785, h2922, h3200, h4, hc12, hc24, hlam, hphi]
                  · linarith only [h2784, h3199, h4, hlam]
                · linarith only [h2783, h3198, h4, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3205 | h3205
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3206 | h3206
      · linarith only [h0, h3206, h4, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3208 | h3208
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3209 | h3209
          · linarith only [h3205, h3206, h3209, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3211 | h3211
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3212 | h3212
              · linarith only [h2783, h2784, h3209, h3211, h3212, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h2783, h2784, h3205, h3206, h3209, h3211, h3212, hc23, hc45, hlam, hphi, ht34]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3215 | h3215
              · linarith only [h2, h2784, h3215, hlam]
              · linarith only [h3206, h3208, h3215, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3218 | h3218
          · linarith only [h3205, h3206, h3218, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3220 | h3220
            · linarith only [h2783, h2784, h3205, h3208, h3218, h3220, hc23, hc45, hlam, hphi, ht34]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3222 | h3222
              · linarith only [h2783, h2784, h3218, h3222, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3224 | h3224
                · linarith only [h0, h3205, h3218, h3224, h4, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h2783, h3224, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3227 | h3227
      · linarith only [h0, h3227, h4, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3229 | h3229
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3230 | h3230
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3231 | h3231
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3232 | h3232
              · linarith only [h2, h2784, h3232, hlam]
              · linarith only [h3227, h3229, h3232, hlam]
            · linarith only [h3205, h3229, h3231, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3236 | h3236
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3237 | h3237
              · linarith only [h2783, h2784, h3205, h3229, h3230, h3237, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h3227, h3229, h3237, hlam]
            · linarith only [h3205, h3229, h3236, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3241 | h3241
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3242 | h3242
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3243 | h3243
              · linarith only [h2, h2784, h3243, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3245 | h3245
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3246 | h3246
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3247 | h3247
                    · linarith only [h1, h2784, h3241, h3247, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h1bigk with h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c | h3249c
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [hlam, p3249_0]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        rcases p3249_3 (m.d 0 1) (by simp) with h3251 | h3251
                        · rcases p3249_3 (m.d 1 2) (by simp) with h3252 | h3252
                          · linarith only [h3252, hlam, p3249_0]
                          · rcases p3249_3 (m.d 1 3) (by simp) with h3254 | h3254
                            · linarith only [h1, h3254, hlam]
                            · linarith only [h3205, h3254, hlam]
                        · linarith only [h3251, hlam, p3249_0]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h3241, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3249_1]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        rcases p3249_3 (m.d 0 1) (by simp) with h3259 | h3259
                        · rcases p3249_3 (m.d 1 2) (by simp) with h3260 | h3260
                          · linarith only [h0, h3260, hlam]
                          · rcases p3249_3 (m.d 1 3) (by simp) with h3262 | h3262
                            · linarith only [h1, h3262, hlam]
                            · linarith only [h3241, h3262, hlam]
                        · linarith only [h3259, hlam, p3249_0]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        rcases p3249_3 (m.d 0 1) (by simp) with h3266 | h3266
                        · rcases p3249_3 (m.d 1 2) (by simp) with h3267 | h3267
                          · linarith only [h0, h3267, hlam]
                          · rcases p3249_3 (m.d 1 3) (by simp) with h3269 | h3269
                            · linarith only [h1, h3269, hlam]
                            · linarith only [h3242, h3269, hlam]
                        · linarith only [h3266, hlam, p3249_0]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h0, hlam, p3249_0]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [hlam, p3249_0]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h3205, hlam, p3249_1]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h3227, hlam, p3249_1]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h3229, hlam, p3249_1]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h1, hlam, p3249_0]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3249_1]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [hlam, p3249_0]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h1, h3227, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3249_1]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h1, h3227, h3243, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3249_1]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h2, hlam, p3249_0]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h2, h2784, h3246, hc12, hc25, hlam, hphi, p3249_1]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h3241, hlam, p3249_1]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [hlam, p3249_0]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h3243, hlam, p3249_1]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h3, hlam, p3249_0]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3249_1]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h3242, hlam, p3249_0]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [h1, h3242, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3249_1]
                      · have p3249_0 := h3249c.1
                        have p3249_1 := h3249c.2.1
                        have p3249_2 := h3249c.2.2.1
                        have p3249_3 := h3249c.2.2.2
                        linarith only [hlam, p3249_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3293 | h3293
                    · linarith only [h0, h3246, h3293, h4, hc12, hc34, hlam, hphi, ht23]
                    · rcases h1bigk with h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c | h3295c
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [hlam, p3295_0]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        rcases p3295_3 (m.d 0 1) (by simp) with h3297 | h3297
                        · rcases p3295_3 (m.d 1 2) (by simp) with h3298 | h3298
                          · linarith only [h3298, hlam, p3295_0]
                          · rcases p3295_3 (m.d 1 3) (by simp) with h3300 | h3300
                            · linarith only [h1, h3300, hlam]
                            · linarith only [h3205, h3300, hlam]
                        · linarith only [h3297, hlam, p3295_0]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h3241, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3295_1]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        rcases p3295_3 (m.d 0 1) (by simp) with h3305 | h3305
                        · rcases p3295_3 (m.d 1 2) (by simp) with h3306 | h3306
                          · linarith only [h0, h3306, hlam]
                          · rcases p3295_3 (m.d 1 3) (by simp) with h3308 | h3308
                            · linarith only [h1, h3308, hlam]
                            · linarith only [h3241, h3308, hlam]
                        · linarith only [h3305, hlam, p3295_0]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        rcases p3295_3 (m.d 0 1) (by simp) with h3312 | h3312
                        · rcases p3295_3 (m.d 1 2) (by simp) with h3313 | h3313
                          · linarith only [h0, h3313, hlam]
                          · rcases p3295_3 (m.d 1 3) (by simp) with h3315 | h3315
                            · linarith only [h1, h3315, hlam]
                            · linarith only [h3242, h3315, hlam]
                        · linarith only [h3312, hlam, p3295_0]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h0, hlam, p3295_0]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [hlam, p3295_0]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h3205, hlam, p3295_1]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h3227, hlam, p3295_1]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h3229, hlam, p3295_1]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h1, hlam, p3295_0]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3295_1]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [hlam, p3295_0]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h1, h3227, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3295_1]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h1, h3227, h3243, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3295_1]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h2, hlam, p3295_0]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3295_1]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h3241, hlam, p3295_1]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [hlam, p3295_0]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h3243, hlam, p3295_1]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h3, hlam, p3295_0]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3295_1]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h3242, hlam, p3295_0]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [h1, h3242, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3295_1]
                      · have p3295_0 := h3295c.1
                        have p3295_1 := h3295c.2.1
                        have p3295_2 := h3295c.2.2.1
                        have p3295_3 := h3295c.2.2.2
                        linarith only [hlam, p3295_0]
                · linarith only [h2783, h2784, h3205, h3245, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3340 | h3340
              · linarith only [h2, h2784, h3340, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3342 | h3342
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3343 | h3343
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3344 | h3344
                    · linarith only [h2784, h3, h3241, h3242, h3344, hlam]
                    · rcases h1bigk with h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c | h3346c
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [hlam, p3346_0]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        rcases p3346_3 (m.d 0 1) (by simp) with h3348 | h3348
                        · rcases p3346_3 (m.d 1 2) (by simp) with h3349 | h3349
                          · linarith only [h3349, hlam, p3346_0]
                          · rcases p3346_3 (m.d 1 3) (by simp) with h3351 | h3351
                            · linarith only [h1, h3351, hlam]
                            · linarith only [h3205, h3351, hlam]
                        · linarith only [h3348, hlam, p3346_0]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h3241, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        rcases p3346_3 (m.d 0 1) (by simp) with h3356 | h3356
                        · rcases p3346_3 (m.d 1 2) (by simp) with h3357 | h3357
                          · linarith only [h0, h3357, hlam]
                          · rcases p3346_3 (m.d 1 3) (by simp) with h3359 | h3359
                            · linarith only [h1, h3359, hlam]
                            · linarith only [h3241, h3359, hlam]
                        · linarith only [h3356, hlam, p3346_0]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h3241, h3242, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h0, hlam, p3346_0]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [hlam, p3346_0]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h3205, hlam, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h3227, hlam, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h3229, hlam, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h1, hlam, p3346_0]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h3242, h3342, h3343, h3344, hc12, hc23, hlam, hphi, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [hlam, p3346_0]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h3242, h3342, h3343, h3344, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h3242, hlam, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h2, hlam, p3346_0]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h3241, hlam, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [hlam, p3346_0]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h3340, hlam, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h3, hlam, p3346_0]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h3, h3241, h3242, h3342, h3343, h3344, hc01, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h2784, h3, h3241, h3342, h3343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [h2784, h3, h3342, h3343, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3346_1]
                      · have p3346_0 := h3346c.1
                        have p3346_1 := h3346c.2.1
                        have p3346_2 := h3346c.2.2.1
                        have p3346_3 := h3346c.2.2.2
                        linarith only [hlam, p3346_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3384 | h3384
                    · linarith only [h0, h3241, h3343, h3384, h4, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [hlam, p3386_0]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        rcases p3386_3 (m.d 0 1) (by simp) with h3388 | h3388
                        · rcases p3386_3 (m.d 1 2) (by simp) with h3389 | h3389
                          · linarith only [h3389, hlam, p3386_0]
                          · rcases p3386_3 (m.d 1 3) (by simp) with h3391 | h3391
                            · linarith only [h1, h3391, hlam]
                            · linarith only [h3205, h3391, hlam]
                        · linarith only [h3388, hlam, p3386_0]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h3241, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        rcases p3386_3 (m.d 0 1) (by simp) with h3396 | h3396
                        · rcases p3386_3 (m.d 1 2) (by simp) with h3397 | h3397
                          · linarith only [h0, h3397, hlam]
                          · rcases p3386_3 (m.d 1 3) (by simp) with h3399 | h3399
                            · linarith only [h1, h3399, hlam]
                            · linarith only [h3241, h3399, hlam]
                        · linarith only [h3396, hlam, p3386_0]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h3241, h3242, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h0, hlam, p3386_0]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [hlam, p3386_0]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h3205, hlam, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h3227, hlam, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h3229, hlam, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h1, hlam, p3386_0]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [hlam, p3386_0]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h3242, hlam, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h2, hlam, p3386_0]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h3241, hlam, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [hlam, p3386_0]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h3340, hlam, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h3, hlam, p3386_0]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h2784, h3, hc13, hc45, hlam, hphi, ht34, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [h2784, h3, hc14, hc45, hlam, hphi, p3386_1]
                      · have p3386_0 := h3386c.1
                        have p3386_1 := h3386c.2.1
                        have p3386_2 := h3386c.2.2.1
                        have p3386_3 := h3386c.2.2.2
                        linarith only [hlam, p3386_0]
                · linarith only [h1, h3205, h3241, h3342, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3425 | h3425
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3426 | h3426
              · linarith only [h2, h2784, h3426, hlam]
              · linarith only [h3241, h3425, h3426, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3429 | h3429
              · linarith only [h2, h2784, h3429, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3431 | h3431
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3432 | h3432
                  · linarith only [h2783, h2784, h3205, h3241, h3431, h3432, hc12, hc23, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3434 | h3434
                    · linarith only [h3432, h3434, h4, hc02, hc34, hlam, hphi, ht23]
                    · rcases h1bigk with h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c | h3436c
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        rcases p3436_3 (m.d 0 1) (by simp) with h3438 | h3438
                        · rcases p3436_3 (m.d 1 2) (by simp) with h3439 | h3439
                          · linarith only [h3439, hlam, p3436_0]
                          · rcases p3436_3 (m.d 1 3) (by simp) with h3441 | h3441
                            · linarith only [h1, h3441, hlam]
                            · linarith only [h3205, h3441, hlam]
                        · linarith only [h3438, hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        rcases p3436_3 (m.d 0 1) (by simp) with h3445 | h3445
                        · rcases p3436_3 (m.d 1 2) (by simp) with h3446 | h3446
                          · linarith only [h0, h3446, hlam]
                          · rcases p3436_3 (m.d 1 3) (by simp) with h3448 | h3448
                            · linarith only [h3448, hlam, p3436_0]
                            · rcases p3436_3 (m.d 1 4) (by simp) with h3450 | h3450
                              · linarith only [h2, h3450, hlam]
                              · linarith only [h3241, h3450, hlam]
                        · linarith only [h3445, hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        rcases p3436_3 (m.d 0 1) (by simp) with h3454 | h3454
                        · rcases p3436_3 (m.d 1 2) (by simp) with h3455 | h3455
                          · linarith only [h0, h3455, hlam]
                          · rcases p3436_3 (m.d 1 3) (by simp) with h3457 | h3457
                            · linarith only [h1, h3457, hlam]
                            · rcases p3436_3 (m.d 1 4) (by simp) with h3459 | h3459
                              · linarith only [h3459, hlam, p3436_0]
                              · rcases p3436_3 (m.d 1 5) (by simp) with h3461 | h3461
                                · linarith only [h3, h3461, hlam]
                                · linarith only [h3429, h3461, hlam]
                        · linarith only [h3454, hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        rcases p3436_3 (m.d 0 1) (by simp) with h3465 | h3465
                        · rcases p3436_3 (m.d 1 2) (by simp) with h3466 | h3466
                          · linarith only [h0, h3466, hlam]
                          · rcases p3436_3 (m.d 1 3) (by simp) with h3468 | h3468
                            · linarith only [h1, h3468, hlam]
                            · rcases p3436_3 (m.d 1 4) (by simp) with h3470 | h3470
                              · linarith only [h2, h3470, hlam]
                              · rcases p3436_3 (m.d 1 5) (by simp) with h3472 | h3472
                                · linarith only [h3472, hlam, p3436_0]
                                · rcases h4bigk with h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c | h3474c
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [hlam, p3474_0]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h3432, h4, hc14, hc45, hlam, hphi, p3474_1]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h4, hlam, p3474_1]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h3432, h4, hc34, hc45, hlam, hphi, p3474_1]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h2784, hlam, p3474_0]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h2, hlam, p3474_0]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [hlam, p3474_0]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h3227, hlam, p3474_1]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h3241, hlam, p3474_1]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h3429, hlam, p3474_0]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h3432, hc04, hc45, hlam, hphi, p3474_1]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h3432, hc14, hc45, hlam, hphi, p3474_1]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [hlam, p3474_0]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h3205, h3241, h3432, hc12, hc45, hlam, hphi, ht23, ht34, p3474_1]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h3432, hlam, p3474_0]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h2783, hlam, p3474_0]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h2783, h3205, h3241, h3432, h4, hc12, hc45, hlam, hphi, ht23, ht34, p3474_1]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h3431, hlam, p3474_0]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [hlam, p3474_0]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h3434, hlam, p3474_0]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h2783, h3205, h3241, hc12, hc45, hlam, hphi, ht23, ht34, p3474_1]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    rcases p3474_3 (m.d 0 4) (by simp) with h3496 | h3496
                                    · linarith only [h2784, h3496, hlam]
                                    · linarith only [h2, h3496, hlam]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h0, h4, hc12, hc45, hlam, hphi, ht23, ht34, p3474_1]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [h3205, h3241, hc12, hc45, hlam, hphi, ht23, ht34, p3474_1]
                                  · have p3474_0 := h3474c.1
                                    have p3474_1 := h3474c.2.1
                                    have p3474_2 := h3474c.2.2.1
                                    have p3474_3 := h3474c.2.2.2
                                    linarith only [hlam, p3474_0]
                        · linarith only [h3465, hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h0, hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h3205, hlam, p3436_1]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h3227, hlam, p3436_1]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h3229, hlam, p3436_1]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h1, hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h2783, h3241, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3436_1]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h3241, hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h3425, hlam, p3436_1]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h2, hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3436_1]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h2783, h2784, h3241, hc13, hc45, hlam, hphi, ht34, p3436_1]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h3429, hlam, p3436_1]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h3, hlam, p3436_0]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3436_1]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h3, h3205, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3436_1]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3436_1]
                      · have p3436_0 := h3436c.1
                        have p3436_1 := h3436c.2.1
                        have p3436_2 := h3436c.2.2.1
                        have p3436_3 := h3436c.2.2.2
                        linarith only [hlam, p3436_0]
                · linarith only [h2783, h2784, h3205, h3431, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
