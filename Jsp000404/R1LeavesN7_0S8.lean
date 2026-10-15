import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 0 1) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 0 1) ∧ (m.d 1 3) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 3) ≤ z)))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  rcases p4721_3 (m.d 0 1) (by simp) with h4724 | h4724
  · rcases p4721_3 (m.d 1 2) (by simp) with h4725 | h4725
    · linarith only [h0, h4725, hlam]
    · rcases p4721_3 (m.d 1 3) (by simp) with h4727 | h4727
      · linarith only [h4727, hlam, p4721_0]
      · rcases p4721_3 (m.d 1 4) (by simp) with h4729 | h4729
        · linarith only [h2, h4729, hlam]
        · rcases p4721_3 (m.d 1 5) (by simp) with h4731 | h4731
          · linarith only [h3, h4731, hlam]
          · rcases h1emax with h4733 | h4733 | h4733 | h4733 | h4733
            · linarith only [h0, h3576, h4, h4131, h4716, h4718, h4733, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h2bigk with h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h3576, h4, h4131, h4716, h4718, hlam, p4735_2]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h0, h3576, h4131, h4716, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4735_1]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h0, h3576, h4131, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4735_1]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                rcases p4735_3 (m.d 0 2) (by simp) with h4740 | h4740
                · rcases p4735_3 (m.d 1 2) (by simp) with h4741 | h4741
                  · linarith only [h0, h4741, hlam]
                  · rcases p4735_3 (m.d 2 3) (by simp) with h4743 | h4743
                    · linarith only [h4, h4743, hlam]
                    · linarith only [h4717, h4743, hlam]
                · linarith only [h4740, hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h0, hlam, p4735_1]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h10, hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h3576, hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h4058, hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h4, hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                rcases p4735_3 (m.d 0 2) (by simp) with h4753 | h4753
                · rcases p4735_3 (m.d 1 2) (by simp) with h4754 | h4754
                  · linarith only [h4754, hlam, p4735_0]
                  · rcases p4735_3 (m.d 2 3) (by simp) with h4756 | h4756
                    · rcases p4735_3 (m.d 2 4) (by simp) with h4757 | h4757
                      · linarith only [h4716, h4757, hlam]
                      · linarith only [h3576, h4757, hlam]
                    · linarith only [h4756, hlam, p4735_0]
                · linarith only [h0, h4753, hlam]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc23, hlam, hphi, p4735_1]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h0, h3576, h4, h4131, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4735_1]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h5, hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                rcases p4735_3 (m.d 0 2) (by simp) with h4766 | h4766
                · rcases p4735_3 (m.d 1 2) (by simp) with h4767 | h4767
                  · linarith only [h4767, hlam, p4735_0]
                  · rcases p4735_3 (m.d 2 3) (by simp) with h4769 | h4769
                    · rcases p4735_3 (m.d 2 4) (by simp) with h4770 | h4770
                      · rcases p4735_3 (m.d 2 5) (by simp) with h4771 | h4771
                        · linarith only [h4718, h4771, hlam]
                        · linarith only [h4058, h4771, hlam]
                      · linarith only [h4770, hlam, p4735_0]
                    · linarith only [h10, h4769, hlam]
                · linarith only [h0, h4766, hlam]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h4716, hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc24, hlam, hphi, p4735_1]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h6, hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                rcases p4735_3 (m.d 0 2) (by simp) with h4781 | h4781
                · rcases p4735_3 (m.d 1 2) (by simp) with h4782 | h4782
                  · linarith only [h4782, hlam, p4735_0]
                  · rcases p4735_3 (m.d 2 3) (by simp) with h4784 | h4784
                    · rcases p4735_3 (m.d 2 4) (by simp) with h4785 | h4785
                      · rcases p4735_3 (m.d 2 5) (by simp) with h4786 | h4786
                        · rcases h4bigk with h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            rcases p4787_3 (m.d 0 4) (by simp) with h4789 | h4789
                            · rcases p4787_3 (m.d 1 4) (by simp) with h4790 | h4790
                              · linarith only [h2, h4790, hlam]
                              · rcases p4787_3 (m.d 2 4) (by simp) with h4792 | h4792
                                · linarith only [h4792, h5, hlam]
                                · linarith only [h3576, h4792, hlam]
                            · linarith only [h2, h4789, hlam]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h3576, h4131, h4718, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4787_1]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            rcases p4787_3 (m.d 0 4) (by simp) with h4797 | h4797
                            · rcases p4787_3 (m.d 1 4) (by simp) with h4798 | h4798
                              · linarith only [h2, h4798, hlam]
                              · linarith only [h4129, h4798, hlam]
                            · linarith only [h4797, h7, hlam]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            rcases p4787_3 (m.d 0 4) (by simp) with h4802 | h4802
                            · rcases p4787_3 (m.d 1 4) (by simp) with h4803 | h4803
                              · linarith only [h2, h4803, hlam]
                              · rcases p4787_3 (m.d 2 4) (by simp) with h4805 | h4805
                                · linarith only [h4805, h5, hlam]
                                · linarith only [h4718, h4805, hlam]
                            · linarith only [h4802, hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h2, hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h3576, hlam, p4787_1]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h4131, h4718, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4787_1]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h4131, hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h5, hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            rcases p4787_3 (m.d 0 4) (by simp) with h4815 | h4815
                            · rcases p4787_3 (m.d 1 4) (by simp) with h4816 | h4816
                              · linarith only [h3576, h4816, hlam]
                              · rcases p4787_3 (m.d 2 4) (by simp) with h4818 | h4818
                                · rcases p4787_3 (m.d 3 4) (by simp) with h4819 | h4819
                                  · linarith only [h4716, h4819, hlam]
                                  · rcases p4787_3 (m.d 4 5) (by simp) with h4821 | h4821
                                    · linarith only [h4718, h4821, hlam]
                                    · linarith only [h4131, h4821, hlam]
                                · linarith only [h3576, h4818, hlam]
                            · linarith only [h2, h4815, hlam]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            rcases p4787_3 (m.d 0 4) (by simp) with h4827 | h4827
                            · rcases p4787_3 (m.d 1 4) (by simp) with h4828 | h4828
                              · linarith only [h3576, h4828, hlam]
                              · linarith only [h4129, h4828, hlam]
                            · linarith only [h4827, h7, hlam]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h0, h3576, h4, h4131, h4716, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4787_1]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h7, hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h4129, hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h4716, hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h4719, hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h9, hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h0, h3576, h4, h4716, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4787_1]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h4718, hlam, p4787_0]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [h0, h4, h4716, h4718, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4787_1]
                          · have p4787_0 := h4787c.1
                            have p4787_1 := h4787c.2.1
                            have p4787_2 := h4787c.2.2.1
                            have p4787_3 := h4787c.2.2.2
                            linarith only [hlam, p4787_0]
                        · linarith only [h4786, hlam, p4735_0]
                      · linarith only [h3576, h4785, hlam]
                    · linarith only [h10, h4784, hlam]
                · linarith only [h0, h4781, hlam]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h4717, hlam, p4735_0]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [h4718, hlam, p4735_1]
              · have p4735_0 := h4735c.1
                have p4735_1 := h4735c.2.1
                have p4735_2 := h4735c.2.2.1
                have p4735_3 := h4735c.2.2.2
                linarith only [hlam, p4735_0]
            · rcases h2bigk with h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h3576, h4, h4131, h4716, h4718, hlam, p4850_2]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h3576, h4131, h4716, h4718, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4850_1]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h0, h3576, h4131, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4850_1]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                rcases p4850_3 (m.d 0 2) (by simp) with h4855 | h4855
                · rcases p4850_3 (m.d 1 2) (by simp) with h4856 | h4856
                  · linarith only [h0, h4856, hlam]
                  · rcases p4850_3 (m.d 2 3) (by simp) with h4858 | h4858
                    · linarith only [h4, h4858, hlam]
                    · linarith only [h4717, h4858, hlam]
                · linarith only [h4855, hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h0, hlam, p4850_1]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h10, hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h3576, hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h4058, hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h4, hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                rcases p4850_3 (m.d 0 2) (by simp) with h4868 | h4868
                · rcases p4850_3 (m.d 1 2) (by simp) with h4869 | h4869
                  · linarith only [h4869, hlam, p4850_0]
                  · rcases p4850_3 (m.d 2 3) (by simp) with h4871 | h4871
                    · rcases p4850_3 (m.d 2 4) (by simp) with h4872 | h4872
                      · linarith only [h4716, h4872, hlam]
                      · linarith only [h3576, h4872, hlam]
                    · linarith only [h4871, hlam, p4850_0]
                · linarith only [h0, h4868, hlam]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc23, hlam, hphi, p4850_1]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4850_1]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h5, hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                rcases p4850_3 (m.d 0 2) (by simp) with h4881 | h4881
                · rcases p4850_3 (m.d 1 2) (by simp) with h4882 | h4882
                  · linarith only [h4882, hlam, p4850_0]
                  · rcases p4850_3 (m.d 2 3) (by simp) with h4884 | h4884
                    · rcases p4850_3 (m.d 2 4) (by simp) with h4885 | h4885
                      · rcases p4850_3 (m.d 2 5) (by simp) with h4886 | h4886
                        · linarith only [h4718, h4886, hlam]
                        · linarith only [h4058, h4886, hlam]
                      · linarith only [h4885, hlam, p4850_0]
                    · linarith only [h10, h4884, hlam]
                · linarith only [h0, h4881, hlam]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h4716, hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc24, hlam, hphi, p4850_1]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h6, hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                rcases p4850_3 (m.d 0 2) (by simp) with h4896 | h4896
                · rcases p4850_3 (m.d 1 2) (by simp) with h4897 | h4897
                  · linarith only [h4897, hlam, p4850_0]
                  · rcases p4850_3 (m.d 2 3) (by simp) with h4899 | h4899
                    · rcases p4850_3 (m.d 2 4) (by simp) with h4900 | h4900
                      · rcases p4850_3 (m.d 2 5) (by simp) with h4901 | h4901
                        · rcases h4bigk with h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c | h4902c
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            rcases p4902_3 (m.d 0 4) (by simp) with h4904 | h4904
                            · rcases p4902_3 (m.d 1 4) (by simp) with h4905 | h4905
                              · linarith only [h2, h4905, hlam]
                              · rcases p4902_3 (m.d 2 4) (by simp) with h4907 | h4907
                                · linarith only [h4907, h5, hlam]
                                · linarith only [h3576, h4907, hlam]
                            · linarith only [h2, h4904, hlam]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h0, h3576, h4, h4131, h4718, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4902_1]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            rcases p4902_3 (m.d 0 4) (by simp) with h4912 | h4912
                            · rcases p4902_3 (m.d 1 4) (by simp) with h4913 | h4913
                              · linarith only [h2, h4913, hlam]
                              · linarith only [h4129, h4913, hlam]
                            · linarith only [h4912, h7, hlam]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            rcases p4902_3 (m.d 0 4) (by simp) with h4917 | h4917
                            · rcases p4902_3 (m.d 1 4) (by simp) with h4918 | h4918
                              · linarith only [h2, h4918, hlam]
                              · rcases p4902_3 (m.d 2 4) (by simp) with h4920 | h4920
                                · linarith only [h4920, h5, hlam]
                                · linarith only [h4718, h4920, hlam]
                            · linarith only [h4917, hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h2, hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h3576, hlam, p4902_1]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h4131, h4718, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4902_1]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h4131, hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h5, hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            rcases p4902_3 (m.d 0 4) (by simp) with h4930 | h4930
                            · rcases p4902_3 (m.d 1 4) (by simp) with h4931 | h4931
                              · linarith only [h3576, h4931, hlam]
                              · rcases p4902_3 (m.d 2 4) (by simp) with h4933 | h4933
                                · rcases p4902_3 (m.d 3 4) (by simp) with h4934 | h4934
                                  · linarith only [h4716, h4934, hlam]
                                  · rcases p4902_3 (m.d 4 5) (by simp) with h4936 | h4936
                                    · linarith only [h4718, h4936, hlam]
                                    · linarith only [h4131, h4936, hlam]
                                · linarith only [h3576, h4933, hlam]
                            · linarith only [h2, h4930, hlam]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            rcases p4902_3 (m.d 0 4) (by simp) with h4942 | h4942
                            · rcases p4902_3 (m.d 1 4) (by simp) with h4943 | h4943
                              · linarith only [h3576, h4943, hlam]
                              · linarith only [h4129, h4943, hlam]
                            · linarith only [h4942, h7, hlam]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h0, h3576, h4, h4131, h4716, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4902_1]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h7, hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h4129, hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h4716, hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h4719, hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h9, hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h0, h3576, h4, h4716, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4902_1]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h4718, hlam, p4902_0]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [h0, h4, h4716, h4718, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4902_1]
                          · have p4902_0 := h4902c.1
                            have p4902_1 := h4902c.2.1
                            have p4902_2 := h4902c.2.2.1
                            have p4902_3 := h4902c.2.2.2
                            linarith only [hlam, p4902_0]
                        · linarith only [h4901, hlam, p4850_0]
                      · linarith only [h3576, h4900, hlam]
                    · linarith only [h10, h4899, hlam]
                · linarith only [h0, h4896, hlam]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h4717, hlam, p4850_0]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [h4718, hlam, p4850_1]
              · have p4850_0 := h4850c.1
                have p4850_1 := h4850c.2.1
                have p4850_2 := h4850c.2.2.1
                have p4850_3 := h4850c.2.2.2
                linarith only [hlam, p4850_0]
            · rcases h2bigk with h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c | h4965c
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h3576, h4, h4131, h4716, h4718, hlam, p4965_2]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h0, h3576, h4131, h4716, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4965_1]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h0, h3576, h4131, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4965_1]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                rcases p4965_3 (m.d 0 2) (by simp) with h4970 | h4970
                · rcases p4965_3 (m.d 1 2) (by simp) with h4971 | h4971
                  · linarith only [h0, h4971, hlam]
                  · rcases p4965_3 (m.d 2 3) (by simp) with h4973 | h4973
                    · linarith only [h4, h4973, hlam]
                    · linarith only [h4717, h4973, hlam]
                · linarith only [h4970, hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h0, hlam, p4965_1]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h10, hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h3576, hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h4058, hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h4, hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                rcases p4965_3 (m.d 0 2) (by simp) with h4983 | h4983
                · rcases p4965_3 (m.d 1 2) (by simp) with h4984 | h4984
                  · linarith only [h4984, hlam, p4965_0]
                  · rcases p4965_3 (m.d 2 3) (by simp) with h4986 | h4986
                    · rcases p4965_3 (m.d 2 4) (by simp) with h4987 | h4987
                      · linarith only [h4716, h4987, hlam]
                      · linarith only [h3576, h4987, hlam]
                    · linarith only [h4986, hlam, p4965_0]
                · linarith only [h0, h4983, hlam]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc23, hlam, hphi, p4965_1]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4965_1]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h5, hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                rcases p4965_3 (m.d 0 2) (by simp) with h4996 | h4996
                · rcases p4965_3 (m.d 1 2) (by simp) with h4997 | h4997
                  · linarith only [h4997, hlam, p4965_0]
                  · rcases p4965_3 (m.d 2 3) (by simp) with h4999 | h4999
                    · rcases p4965_3 (m.d 2 4) (by simp) with h5000 | h5000
                      · rcases p4965_3 (m.d 2 5) (by simp) with h5001 | h5001
                        · linarith only [h4718, h5001, hlam]
                        · linarith only [h4058, h5001, hlam]
                      · linarith only [h5000, hlam, p4965_0]
                    · linarith only [h10, h4999, hlam]
                · linarith only [h0, h4996, hlam]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h4716, hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc24, hlam, hphi, p4965_1]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h6, hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                rcases p4965_3 (m.d 0 2) (by simp) with h5011 | h5011
                · rcases p4965_3 (m.d 1 2) (by simp) with h5012 | h5012
                  · linarith only [h5012, hlam, p4965_0]
                  · rcases p4965_3 (m.d 2 3) (by simp) with h5014 | h5014
                    · rcases p4965_3 (m.d 2 4) (by simp) with h5015 | h5015
                      · rcases p4965_3 (m.d 2 5) (by simp) with h5016 | h5016
                        · rcases h4bigk with h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            rcases p5017_3 (m.d 0 4) (by simp) with h5019 | h5019
                            · rcases p5017_3 (m.d 1 4) (by simp) with h5020 | h5020
                              · linarith only [h2, h5020, hlam]
                              · rcases p5017_3 (m.d 2 4) (by simp) with h5022 | h5022
                                · linarith only [h5, h5022, hlam]
                                · linarith only [h3576, h5022, hlam]
                            · linarith only [h2, h5019, hlam]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h3576, h4131, h4718, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5017_1]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            rcases p5017_3 (m.d 0 4) (by simp) with h5027 | h5027
                            · rcases p5017_3 (m.d 1 4) (by simp) with h5028 | h5028
                              · linarith only [h2, h5028, hlam]
                              · linarith only [h4129, h5028, hlam]
                            · linarith only [h5027, h7, hlam]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            rcases p5017_3 (m.d 0 4) (by simp) with h5032 | h5032
                            · rcases p5017_3 (m.d 1 4) (by simp) with h5033 | h5033
                              · linarith only [h2, h5033, hlam]
                              · rcases p5017_3 (m.d 2 4) (by simp) with h5035 | h5035
                                · linarith only [h5, h5035, hlam]
                                · linarith only [h4718, h5035, hlam]
                            · linarith only [h5032, hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h2, hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h3576, hlam, p5017_1]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h4131, h4718, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5017_1]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h4131, hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h5, hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            rcases p5017_3 (m.d 0 4) (by simp) with h5045 | h5045
                            · rcases p5017_3 (m.d 1 4) (by simp) with h5046 | h5046
                              · linarith only [h3576, h5046, hlam]
                              · rcases p5017_3 (m.d 2 4) (by simp) with h5048 | h5048
                                · rcases p5017_3 (m.d 3 4) (by simp) with h5049 | h5049
                                  · linarith only [h4716, h5049, hlam]
                                  · rcases p5017_3 (m.d 4 5) (by simp) with h5051 | h5051
                                    · linarith only [h4718, h5051, hlam]
                                    · linarith only [h4131, h5051, hlam]
                                · linarith only [h3576, h5048, hlam]
                            · linarith only [h2, h5045, hlam]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            rcases p5017_3 (m.d 0 4) (by simp) with h5057 | h5057
                            · rcases p5017_3 (m.d 1 4) (by simp) with h5058 | h5058
                              · linarith only [h3576, h5058, hlam]
                              · linarith only [h4129, h5058, hlam]
                            · linarith only [h5057, h7, hlam]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h0, h3576, h4, h4131, h4716, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5017_1]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h7, hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h4129, hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h4716, hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h4719, hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h9, hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h0, h3576, h4, h4716, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5017_1]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h4718, hlam, p5017_0]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [h0, h4, h4716, h4718, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5017_1]
                          · have p5017_0 := h5017c.1
                            have p5017_1 := h5017c.2.1
                            have p5017_2 := h5017c.2.2.1
                            have p5017_3 := h5017c.2.2.2
                            linarith only [hlam, p5017_0]
                        · linarith only [h5016, hlam, p4965_0]
                      · linarith only [h3576, h5015, hlam]
                    · linarith only [h10, h5014, hlam]
                · linarith only [h0, h5011, hlam]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h4717, hlam, p4965_0]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [h4718, hlam, p4965_1]
              · have p4965_0 := h4965c.1
                have p4965_1 := h4965c.2.1
                have p4965_2 := h4965c.2.2.1
                have p4965_3 := h4965c.2.2.2
                linarith only [hlam, p4965_0]
            · rcases h2bigk with h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h3576, h4, h4131, h4716, h4718, hlam, p5080_2]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h0, h3576, h4131, h4716, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5080_1]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h0, h3576, h4131, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5080_1]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                rcases p5080_3 (m.d 0 2) (by simp) with h5085 | h5085
                · rcases p5080_3 (m.d 1 2) (by simp) with h5086 | h5086
                  · linarith only [h0, h5086, hlam]
                  · rcases p5080_3 (m.d 2 3) (by simp) with h5088 | h5088
                    · linarith only [h4, h5088, hlam]
                    · linarith only [h4717, h5088, hlam]
                · linarith only [h5085, hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h0, hlam, p5080_1]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h10, hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h3576, hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h4058, hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h4, hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                rcases p5080_3 (m.d 0 2) (by simp) with h5098 | h5098
                · rcases p5080_3 (m.d 1 2) (by simp) with h5099 | h5099
                  · linarith only [h5099, hlam, p5080_0]
                  · rcases p5080_3 (m.d 2 3) (by simp) with h5101 | h5101
                    · rcases p5080_3 (m.d 2 4) (by simp) with h5102 | h5102
                      · linarith only [h4716, h5102, hlam]
                      · linarith only [h3576, h5102, hlam]
                    · linarith only [h5101, hlam, p5080_0]
                · linarith only [h0, h5098, hlam]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc23, hlam, hphi, p5080_1]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5080_1]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h5, hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                rcases p5080_3 (m.d 0 2) (by simp) with h5111 | h5111
                · rcases p5080_3 (m.d 1 2) (by simp) with h5112 | h5112
                  · linarith only [h5112, hlam, p5080_0]
                  · rcases p5080_3 (m.d 2 3) (by simp) with h5114 | h5114
                    · rcases p5080_3 (m.d 2 4) (by simp) with h5115 | h5115
                      · rcases p5080_3 (m.d 2 5) (by simp) with h5116 | h5116
                        · linarith only [h4718, h5116, hlam]
                        · linarith only [h4058, h5116, hlam]
                      · linarith only [h5115, hlam, p5080_0]
                    · linarith only [h10, h5114, hlam]
                · linarith only [h0, h5111, hlam]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h4716, hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc24, hlam, hphi, p5080_1]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h6, hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                rcases p5080_3 (m.d 0 2) (by simp) with h5126 | h5126
                · rcases p5080_3 (m.d 1 2) (by simp) with h5127 | h5127
                  · linarith only [h5127, hlam, p5080_0]
                  · rcases p5080_3 (m.d 2 3) (by simp) with h5129 | h5129
                    · rcases p5080_3 (m.d 2 4) (by simp) with h5130 | h5130
                      · rcases p5080_3 (m.d 2 5) (by simp) with h5131 | h5131
                        · rcases h4bigk with h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c | h5132c
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            rcases p5132_3 (m.d 0 4) (by simp) with h5134 | h5134
                            · rcases p5132_3 (m.d 1 4) (by simp) with h5135 | h5135
                              · linarith only [h2, h5135, hlam]
                              · rcases p5132_3 (m.d 2 4) (by simp) with h5137 | h5137
                                · linarith only [h5, h5137, hlam]
                                · linarith only [h3576, h5137, hlam]
                            · linarith only [h2, h5134, hlam]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h0, h3576, h4, h4131, h4718, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5132_1]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            rcases p5132_3 (m.d 0 4) (by simp) with h5142 | h5142
                            · rcases p5132_3 (m.d 1 4) (by simp) with h5143 | h5143
                              · linarith only [h2, h5143, hlam]
                              · linarith only [h4129, h5143, hlam]
                            · linarith only [h5142, h7, hlam]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            rcases p5132_3 (m.d 0 4) (by simp) with h5147 | h5147
                            · rcases p5132_3 (m.d 1 4) (by simp) with h5148 | h5148
                              · linarith only [h2, h5148, hlam]
                              · rcases p5132_3 (m.d 2 4) (by simp) with h5150 | h5150
                                · linarith only [h5, h5150, hlam]
                                · linarith only [h4718, h5150, hlam]
                            · linarith only [h5147, hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h2, hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h3576, hlam, p5132_1]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h4131, h4718, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5132_1]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h4131, hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h5, hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            rcases p5132_3 (m.d 0 4) (by simp) with h5160 | h5160
                            · rcases p5132_3 (m.d 1 4) (by simp) with h5161 | h5161
                              · linarith only [h3576, h5161, hlam]
                              · rcases p5132_3 (m.d 2 4) (by simp) with h5163 | h5163
                                · rcases p5132_3 (m.d 3 4) (by simp) with h5164 | h5164
                                  · linarith only [h4716, h5164, hlam]
                                  · rcases p5132_3 (m.d 4 5) (by simp) with h5166 | h5166
                                    · linarith only [h4718, h5166, hlam]
                                    · linarith only [h4131, h5166, hlam]
                                · linarith only [h3576, h5163, hlam]
                            · linarith only [h2, h5160, hlam]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            rcases p5132_3 (m.d 0 4) (by simp) with h5172 | h5172
                            · rcases p5132_3 (m.d 1 4) (by simp) with h5173 | h5173
                              · linarith only [h3576, h5173, hlam]
                              · linarith only [h4129, h5173, hlam]
                            · linarith only [h5172, h7, hlam]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h0, h3576, h4, h4131, h4716, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5132_1]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h7, hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h4129, hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h4716, hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h4719, hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h9, hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h0, h3576, h4, h4716, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5132_1]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h4718, hlam, p5132_0]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [h0, h4, h4716, h4718, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5132_1]
                          · have p5132_0 := h5132c.1
                            have p5132_1 := h5132c.2.1
                            have p5132_2 := h5132c.2.2.1
                            have p5132_3 := h5132c.2.2.2
                            linarith only [hlam, p5132_0]
                        · linarith only [h5131, hlam, p5080_0]
                      · linarith only [h3576, h5130, hlam]
                    · linarith only [h10, h5129, hlam]
                · linarith only [h0, h5126, hlam]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h4717, hlam, p5080_0]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [h4718, hlam, p5080_1]
              · have p5080_0 := h5080c.1
                have p5080_1 := h5080c.2.1
                have p5080_2 := h5080c.2.2.1
                have p5080_3 := h5080c.2.2.2
                linarith only [hlam, p5080_0]
  · linarith only [h4724, hlam, p4721_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 0 1) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 0 1) ∧ (m.d 1 4) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 4) ≤ z)))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h0, h4, h4131, h4716, h4718, hlam, p4721_2]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 0 1) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 0 1) ∧ (m.d 1 5) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 5) ≤ z)))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  rcases p4721_3 (m.d 0 1) (by simp) with h5197 | h5197
  · rcases p4721_3 (m.d 1 2) (by simp) with h5198 | h5198
    · linarith only [h0, h5198, hlam]
    · rcases p4721_3 (m.d 1 3) (by simp) with h5200 | h5200
      · linarith only [h1, h5200, hlam]
      · linarith only [h4130, h5200, hlam]
  · linarith only [h5197, hlam, p4721_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 2) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 2) ∧ (m.d 0 1) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 0 1) ≤ z)))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h0, hlam, p4721_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 2) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 2) ∧ (m.d 1 2) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 2) ≤ z)))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [hlam, p4721_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x7 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 2) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 2) ∧ (m.d 1 3) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 3) ≤ z)))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h10, hlam, p4721_1]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x8 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 2) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 2) ∧ (m.d 1 4) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 4) ≤ z)))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h3576, hlam, p4721_1]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x9 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 2) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 2) ∧ (m.d 1 5) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 5) ≤ z)))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h4058, hlam, p4721_1]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x10 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 3) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 3) ∧ (m.d 0 1) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 0 1) ≤ z)))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h1, hlam, p4721_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x11 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 3) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 3) ∧ (m.d 1 2) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 2) ≤ z)))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  rcases p4721_3 (m.d 0 1) (by simp) with h5210 | h5210
  · rcases p4721_3 (m.d 1 2) (by simp) with h5211 | h5211
    · linarith only [h10, h5211, hlam]
    · rcases p4721_3 (m.d 1 3) (by simp) with h5213 | h5213
      · rcases p4721_3 (m.d 1 4) (by simp) with h5214 | h5214
        · linarith only [h4129, h5214, hlam]
        · linarith only [h3576, h5214, hlam]
      · linarith only [h10, h5213, hlam]
  · linarith only [h0, h5210, hlam]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x12 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 3) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 3) ∧ (m.d 1 3) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 3) ≤ z)))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [hlam, p4721_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x13 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 3) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 3) ∧ (m.d 1 4) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 4) ≤ z)))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  rcases p4721_3 (m.d 0 1) (by simp) with h5220 | h5220
  · rcases p4721_3 (m.d 1 2) (by simp) with h5221 | h5221
    · linarith only [h10, h5221, hlam]
    · rcases p4721_3 (m.d 1 3) (by simp) with h5223 | h5223
      · rcases p4721_3 (m.d 1 4) (by simp) with h5224 | h5224
        · linarith only [h4129, h5224, hlam]
        · rcases p4721_3 (m.d 1 5) (by simp) with h5226 | h5226
          · linarith only [h4130, h5226, hlam]
          · linarith only [h4131, h5226, hlam]
      · linarith only [h4129, h5223, hlam]
  · linarith only [h2, h5220, hlam]

end R2N4
