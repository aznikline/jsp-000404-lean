import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10174000 in
set_option maxHeartbeats 10174000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3397 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3738 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h3739 | h3739
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3740 | h3740
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3741 | h3741
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3742 | h3742
        · linarith only [h0, h3742, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3744 | h3744
          · linarith only [h0, h3397, h3738, h3744, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3746 | h3746
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3747 | h3747
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3748 | h3748
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3749 | h3749
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3750 | h3750
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3751 | h3751
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3752 | h3752
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3753 | h3753
                          · rcases h0bigk with h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [hlam, p3754_0]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h0, h3746, h3751, h3753, hc01, hc45, hlam, hphi, ht0b, ht5b, p3754_1]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h2, h3739, h3744, h3746, h3751, h3753, hc01, hc45, hlam, hphi, ht0b, ht5b, p3754_1]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h2, h3744, h3746, h3751, h3753, hc01, hc45, hlam, hphi, ht0b, ht5b, p3754_1]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              rcases p3754_3 (m.d 0 1) (by simp) with h3759 | h3759
                              · rcases p3754_3 (m.d 0 2) (by simp) with h3760 | h3760
                                · linarith only [h0, h3760, hlam]
                                · linarith only [h3738, h3760, hlam]
                              · linarith only [h3, h3759, hlam]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h0, hlam, p3754_0]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [hlam, p3754_0]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h4, hlam, p3754_0]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h3397, hlam, p3754_1]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h3, h3397, h3750, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3754_1]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h1, hlam, p3754_1]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p3754_1]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [hlam, p3754_0]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h2, h3744, h3746, h3751, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p3754_1]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              rcases p3754_3 (m.d 0 1) (by simp) with h3773 | h3773
                              · rcases p3754_3 (m.d 0 2) (by simp) with h3774 | h3774
                                · linarith only [h3774, h4, hlam]
                                · linarith only [h3738, h3774, hlam]
                              · linarith only [h3, h3773, hlam]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h2, hlam, p3754_0]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h0, h3746, h3751, h3753, hc04, hc45, hlam, hphi, ht0b, ht5b, p3754_1]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h3739, hlam, p3754_0]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [hlam, p3754_0]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              rcases p3754_3 (m.d 0 1) (by simp) with h3782 | h3782
                              · rcases p3754_3 (m.d 0 2) (by simp) with h3783 | h3783
                                · linarith only [h3397, h3783, hlam]
                                · linarith only [h3738, h3783, hlam]
                              · linarith only [h3, h3782, hlam]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h3, hlam, p3754_0]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h3738, hlam, p3754_1]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h3740, hlam, p3754_0]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [h3741, hlam, p3754_1]
                            · have p3754_0 := h3754c.1
                              have p3754_1 := h3754c.2.1
                              have p3754_2 := h3754c.2.2.1
                              have p3754_3 := h3754c.2.2.2
                              linarith only [hlam, p3754_0]
                          · rcases h0bigk with h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [hlam, p3792_0]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h0, h3746, hc01, hc25, hlam, hphi, ht0b, ht5b, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h0, h3746, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h2, h3744, h3746, hc01, hc25, hlam, hphi, ht0b, ht5b, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h3741, h3753, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h0, hlam, p3792_0]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [hlam, p3792_0]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h4, hlam, p3792_0]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h3397, hlam, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h1, hlam, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h0, h3746, hc03, hc25, hlam, hphi, ht0b, ht5b, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [hlam, p3792_0]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h3741, h3753, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h3741, h3753, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h2, hlam, p3792_0]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h3738, h3741, h3753, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h3739, hlam, p3792_0]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [hlam, p3792_0]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h3397, h3741, h3750, h3753, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h3, hlam, p3792_0]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h3738, hlam, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h3740, hlam, p3792_0]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [h3741, hlam, p3792_1]
                            · have p3792_0 := h3792c.1
                              have p3792_1 := h3792c.2.1
                              have p3792_2 := h3792c.2.2.1
                              have p3792_3 := h3792c.2.2.2
                              linarith only [hlam, p3792_0]
                        · linarith only [h3397, h3741, h3752, hlam]
                      · linarith only [h3740, h3751, h4, hlam]
                    · linarith only [h0, h3739, h3746, h3750, h4, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h3744, h3746, h3749, hlam]
                · linarith only [h3744, h3746, h3747, h3748, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3823 | h3823
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3824 | h3824
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3825 | h3825
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3826 | h3826
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3827 | h3827
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3828 | h3828
                          · rcases h0bigk with h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c | h3829c
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [hlam, p3829_0]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h0, h3746, hc01, hc25, hlam, hphi, ht0b, ht5b, p3829_1]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h3739, h3742, h3746, h3747, h3826, h3828, hc01, hc45, hlam, hphi, ht0b, ht5b, p3829_1]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h3739, h3742, h3746, h3747, h3826, h3828, hc01, hc45, hlam, hphi, ht0b, ht5b, p3829_1]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              rcases p3829_3 (m.d 0 1) (by simp) with h3834 | h3834
                              · rcases p3829_3 (m.d 0 2) (by simp) with h3835 | h3835
                                · linarith only [h0, h3835, hlam]
                                · linarith only [h3738, h3835, hlam]
                              · linarith only [h3, h3834, hlam]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h0, hlam, p3829_0]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [hlam, p3829_0]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h4, hlam, p3829_0]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h3397, hlam, p3829_1]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3829_1]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h1, hlam, p3829_1]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h0, h3746, h3826, h3828, hc03, hc45, hlam, hphi, ht0b, ht5b, p3829_1]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [hlam, p3829_0]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h3739, h3742, h3746, h3747, h3826, h3828, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3829_1]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              rcases p3829_3 (m.d 0 1) (by simp) with h3848 | h3848
                              · rcases p3829_3 (m.d 0 2) (by simp) with h3849 | h3849
                                · linarith only [h3849, h4, hlam]
                                · linarith only [h3738, h3849, hlam]
                              · linarith only [h3, h3848, hlam]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h2, hlam, p3829_0]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h0, h3746, h3826, h3828, hc04, hc45, hlam, hphi, ht0b, ht5b, p3829_1]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h3739, hlam, p3829_0]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [hlam, p3829_0]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              rcases p3829_3 (m.d 0 1) (by simp) with h3857 | h3857
                              · rcases p3829_3 (m.d 0 2) (by simp) with h3858 | h3858
                                · linarith only [h3397, h3858, hlam]
                                · linarith only [h3738, h3858, hlam]
                              · linarith only [h3, h3857, hlam]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h3, hlam, p3829_0]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h3738, hlam, p3829_1]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h3740, hlam, p3829_0]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [h3741, hlam, p3829_1]
                            · have p3829_0 := h3829c.1
                              have p3829_1 := h3829c.2.1
                              have p3829_2 := h3829c.2.2.1
                              have p3829_3 := h3829c.2.2.2
                              linarith only [hlam, p3829_0]
                          · linarith only [h3739, h3741, h3742, h3746, h3747, h3826, h3828, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h3397, h3741, h3827, hlam]
                      · linarith only [h3739, h3742, h3747, h3826, h4, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h3739, h3825, h4, hlam]
                  · linarith only [h3742, h3746, h3747, h3824, hlam]
                · linarith only [h3742, h3746, h3823, hlam]
            · linarith only [h3738, h3746, h4, hc12, hc23, hlam, hphi]
      · linarith only [h3397, h3738, h3741, hlam]
    · linarith only [h3397, h3738, h3739, h3740, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3876 | h3876
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3877 | h3877
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3878 | h3878
        · linarith only [h0, h3878, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3880 | h3880
          · linarith only [h0, h3397, h3738, h3880, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3882 | h3882
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3883 | h3883
              · linarith only [h1, h3739, h3883, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3885 | h3885
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3886 | h3886
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3887 | h3887
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3888 | h3888
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3889 | h3889
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3890 | h3890
                          · rcases h0bigk with h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h0, h3882, h3888, h3890, hc01, hc45, hlam, hphi, ht0b, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h0, h3882, h3888, h3890, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h0, h3739, h3882, h3888, h3890, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              rcases p3891_3 (m.d 0 1) (by simp) with h3896 | h3896
                              · rcases p3891_3 (m.d 0 2) (by simp) with h3897 | h3897
                                · linarith only [h0, h3897, hlam]
                                · linarith only [h3738, h3897, hlam]
                              · linarith only [h3, h3896, hlam]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h0, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h4, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3397, hlam, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3739, h3887, h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h1, hlam, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3739, h3887, hc02, hc23, hlam, hphi, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3739, hlam, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3738, h3739, h3887, h3888, h3890, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h2, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h0, h3882, h3888, h3890, hc04, hc45, hlam, hphi, ht0b, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3739, h3887, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3738, h3739, h3887, h3888, h3890, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3738, hlam, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3876, hlam, p3891_0]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [h3877, hlam, p3891_1]
                            · have p3891_0 := h3891c.1
                              have p3891_1 := h3891c.2.1
                              have p3891_2 := h3891c.2.2.1
                              have p3891_3 := h3891c.2.2.2
                              linarith only [hlam, p3891_0]
                          · linarith only [h0, h3739, h3877, h3882, h3888, h3890, h4, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h3, h3397, h3882, h3886, h3888, h3889, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h3739, h3887, h3888, h4, hc02, hc35, hlam, hphi, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3924 | h3924
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3925 | h3925
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3926 | h3926
                          · rcases h0bigk with h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [hlam, p3927_0]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h0, h3882, hc01, hc25, hlam, hphi, ht0b, ht5b, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h0, h3882, h3924, h3926, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h0, h3397, h3882, h3924, h3926, hc01, hc45, hlam, hphi, ht0b, ht5b, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              rcases p3927_3 (m.d 0 1) (by simp) with h3932 | h3932
                              · rcases p3927_3 (m.d 0 2) (by simp) with h3933 | h3933
                                · linarith only [h0, h3933, hlam]
                                · linarith only [h3738, h3933, hlam]
                              · linarith only [h3, h3932, hlam]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h0, hlam, p3927_0]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [hlam, p3927_0]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h4, hlam, p3927_0]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h3397, hlam, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h3887, h4, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h1, hlam, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h0, h3739, h3882, hc04, hc25, hlam, hphi, ht0b, ht5b, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [hlam, p3927_0]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h3739, hlam, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h3738, h3887, h3924, h3926, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h2, hlam, p3927_0]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h3397, h3887, hc02, hc34, hlam, hphi, ht23, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h3397, h3887, hc03, hc34, hlam, hphi, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [hlam, p3927_0]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              rcases p3927_3 (m.d 0 1) (by simp) with h3951 | h3951
                              · rcases p3927_3 (m.d 0 2) (by simp) with h3952 | h3952
                                · linarith only [h3397, h3952, hlam]
                                · linarith only [h3738, h3952, hlam]
                              · linarith only [h3, h3951, hlam]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h3, hlam, p3927_0]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h3738, hlam, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h3876, hlam, p3927_0]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [h3877, hlam, p3927_1]
                            · have p3927_0 := h3927c.1
                              have p3927_1 := h3927c.2.1
                              have p3927_2 := h3927c.2.2.1
                              have p3927_3 := h3927c.2.2.2
                              linarith only [hlam, p3927_0]
                          · linarith only [h3887, h3926, h4, hc02, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h3, h3397, h3882, h3886, h3924, h3925, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h3876, h3882, h3924, h4, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h3878, h3882, h3883, h3886, hlam]
                · linarith only [h3739, h3876, h3878, h3882, h3885, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
            · linarith only [h3738, h3739, h3882, h4, hc12, hc34, hlam, hphi, ht23]
      · linarith only [h3738, h3739, h3877, h4, hlam]
    · linarith only [h3738, h3876, h4, hlam]

end R2N4
