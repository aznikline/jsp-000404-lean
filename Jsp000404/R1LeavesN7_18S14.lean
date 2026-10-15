import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8272 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h9441 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h9778 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 3 4 (by decide) (by decide) with h9779 | h9779
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9780 | h9780
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9781 | h9781
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9782 | h9782
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9783 | h9783
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9784 | h9784
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9785 | h9785
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9786 | h9786
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9787 | h9787
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9788 | h9788
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9789 | h9789
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9790 | h9790
                        · rcases h0bigk with h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [hlam, p9791_0]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h0, hlam, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h5743, hlam, p9791_0]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h6852, hlam, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h7594, hlam, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h9441, h9782, h9787, hc01, hc12, hlam, hphi, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [hlam, p9791_0]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h8272, hlam, p9791_0]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h9441, hlam, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h9441, h9782, h9787, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h5743, h9782, hc01, hc12, hlam, hphi, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h8272, h9782, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [hlam, p9791_0]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h8272, h9782, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h7594, h8272, h9782, hc01, hc12, hlam, hphi, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h6852, hc01, hc14, hlam, hphi, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h9441, h9778, h9782, h9787, h9788, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h9779, hlam, p9791_0]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [hlam, p9791_0]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h7594, h9441, h9782, h9787, hc01, hc12, hlam, hphi, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h7594, hc01, hc15, hlam, hphi, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h9778, hlam, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h9780, hlam, p9791_0]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [h9781, hlam, p9791_1]
                          · have p9791_0 := h9791c.1
                            have p9791_1 := h9791c.2.1
                            have p9791_2 := h9791c.2.2.1
                            have p9791_3 := h9791c.2.2.2
                            linarith only [hlam, p9791_0]
                        · linarith only [h9441, h9778, h9782, h9787, h9789, h9790, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h9441, h9781, h9789, hlam]
                    · linarith only [h8272, h9780, h9788, hlam]
                  · linarith only [h8272, h9779, h9787, hlam]
                · linarith only [h5743, h9441, h9778, h9780, h9786, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h8272, h9778, h9779, h9782, h9785, hc03, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h8272, h9778, h9782, h9784, hlam]
          · linarith only [h8272, h9778, h9782, h9783, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9825 | h9825
          · linarith only [h9441, h9778, h9782, h9825, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9827 | h9827
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9828 | h9828
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9829 | h9829
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9830 | h9830
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9831 | h9831
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9832 | h9832
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9833 | h9833
                        · rcases h0bigk with h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [hlam, p9834_0]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h0, hlam, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h5743, hlam, p9834_0]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h6852, hlam, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h7594, hlam, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h0, h9825, h9830, hc01, hc23, hlam, hphi, ht12, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [hlam, p9834_0]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h8272, hlam, p9834_0]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h9441, hlam, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h0, h9825, h9830, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h5743, h9782, hc01, hc23, hlam, hphi, ht12, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h5743, h9782, hc02, hc23, hlam, hphi, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [hlam, p9834_0]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h5743, h9441, h9778, h9782, h9831, h9833, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h5743, h7594, h9782, hc01, hc23, hlam, hphi, ht12, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h6852, hc01, hc14, hlam, hphi, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h9441, h9778, h9830, h9831, h9833, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h9779, hlam, p9834_0]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [hlam, p9834_0]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h5743, h7594, h9779, h9782, hc01, hc23, hlam, hphi, ht12, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h7594, hc01, hc15, hlam, hphi, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h9778, hlam, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h9780, hlam, p9834_0]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [h9781, hlam, p9834_1]
                          · have p9834_0 := h9834c.1
                            have p9834_1 := h9834c.2.1
                            have p9834_2 := h9834c.2.2.1
                            have p9834_3 := h9834c.2.2.2
                            linarith only [hlam, p9834_0]
                        · rcases h0bigk with h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c | h9860c
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [hlam, p9860_0]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h0, hlam, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h5743, hlam, p9860_0]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h6852, hlam, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h7594, hlam, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h0, h9825, h9830, hc01, hc23, hlam, hphi, ht12, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [hlam, p9860_0]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h8272, hlam, p9860_0]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h9441, hlam, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h0, h9825, h9830, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h5743, h9782, hc01, hc23, hlam, hphi, ht12, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h5743, h9782, hc02, hc23, hlam, hphi, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [hlam, p9860_0]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h5743, h6852, h9782, hc01, hc23, hlam, hphi, ht12, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h5743, h7594, h9782, hc01, hc23, hlam, hphi, ht12, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h6852, h9825, h9830, hc01, hc23, hlam, hphi, ht12, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h6852, h9778, h9825, h9830, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h9779, hlam, p9860_0]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [hlam, p9860_0]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h6852, h7594, h9825, h9830, hc01, hc23, hlam, hphi, ht12, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h7594, h9825, h9827, h9830, hc01, hc23, hlam, hphi, ht12, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h9778, hlam, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h9780, hlam, p9860_0]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [h9781, hlam, p9860_1]
                          · have p9860_0 := h9860c.1
                            have p9860_1 := h9860c.2.1
                            have p9860_2 := h9860c.2.2.1
                            have p9860_3 := h9860c.2.2.2
                            linarith only [hlam, p9860_0]
                      · linarith only [h0, h9825, h9832, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h5743, h9780, h9782, h9831, hlam]
                  · linarith only [h5743, h9779, h9782, h9830, hlam]
                · linarith only [h5743, h9780, h9829, hlam]
              · linarith only [h5743, h9779, h9828, hlam]
            · linarith only [h0, h9778, h9827, hlam]
      · linarith only [h9441, h9778, h9781, hlam]
    · linarith only [h9441, h9778, h9779, h9780, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9894 | h9894
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9895 | h9895
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9896 | h9896
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9897 | h9897
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9898 | h9898
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9899 | h9899
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9900 | h9900
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9901 | h9901
                  · linarith only [h8272, h9778, h9779, h9896, h9901, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h8272, h9778, h9896, h9899, h9901, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h5743, h9894, h9900, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9905 | h9905
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9906 | h9906
                  · linarith only [h8272, h9778, h9779, h9896, h9906, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9908 | h9908
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9909 | h9909
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9910 | h9910
                        · rcases h0bigk with h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c | h9911c
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [hlam, p9911_0]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h0, hlam, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h5743, hlam, p9911_0]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h6852, hlam, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h7594, hlam, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [hlam, p9911_0]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h8272, hlam, p9911_0]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h9441, hlam, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h5743, h8272, h9899, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h5743, h9899, hc01, hc34, hlam, hphi, ht12, ht23, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h5743, h9899, hc02, hc34, hlam, hphi, ht23, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [hlam, p9911_0]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h9779, hlam, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h7594, h8272, h9896, h9899, hc01, hc34, hlam, hphi, ht12, ht23, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h9441, h9897, hc01, hc12, hlam, hphi, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h9441, h9778, h9897, h9908, h9910, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h9441, h9897, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [hlam, p9911_0]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h7594, h9441, h9897, hc01, hc12, hlam, hphi, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h7594, hc01, hc15, hlam, hphi, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h9778, hlam, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h9894, hlam, p9911_0]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [h9895, hlam, p9911_1]
                          · have p9911_0 := h9911c.1
                            have p9911_1 := h9911c.2.1
                            have p9911_2 := h9911c.2.2.1
                            have p9911_3 := h9911c.2.2.2
                            linarith only [hlam, p9911_0]
                        · linarith only [h8272, h9778, h9896, h9899, h9908, h9910, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h6852, h8272, h9441, h9778, h9895, h9896, h9899, h9909, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h8272, h9778, h9779, h9894, h9908, hc04, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h8272, h9778, h9894, h9896, h9905, hlam]
            · linarith only [h8272, h9441, h9778, h9896, h9897, h9898, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h8272, h9896, h9897, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9943 | h9943
          · linarith only [h9441, h9778, h9896, h9943, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9945 | h9945
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9946 | h9946
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9947 | h9947
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9948 | h9948
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9949 | h9949
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9950 | h9950
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9951 | h9951
                        · rcases h0bigk with h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [hlam, p9952_0]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h0, hlam, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h5743, hlam, p9952_0]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h6852, hlam, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h7594, hlam, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h0, h9943, h9948, hc01, hc23, hlam, hphi, ht12, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [hlam, p9952_0]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h8272, hlam, p9952_0]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h9441, hlam, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h0, h9943, h9948, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h9779, h9896, h9946, hc01, hc23, hlam, hphi, ht12, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h9779, h9896, h9946, hc02, hc23, hlam, hphi, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [hlam, p9952_0]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h9779, hlam, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h7594, h9779, h9896, h9946, hc01, hc23, hlam, hphi, ht12, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h6852, hc01, hc14, hlam, hphi, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h9441, h9778, h9948, h9949, h9951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h9779, h9896, h9946, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [hlam, p9952_0]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h7594, h9779, h9896, h9946, hc01, hc23, hlam, hphi, ht12, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h7594, hc01, hc15, hlam, hphi, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h9778, hlam, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h9894, hlam, p9952_0]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [h9895, hlam, p9952_1]
                          · have p9952_0 := h9952c.1
                            have p9952_1 := h9952c.2.1
                            have p9952_2 := h9952c.2.2.1
                            have p9952_3 := h9952c.2.2.2
                            linarith only [hlam, p9952_0]
                        · linarith only [h9779, h9895, h9951, hlam]
                      · linarith only [h8272, h9778, h9779, h9895, h9943, h9946, h9950, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h8272, h9779, h9896, h9946, h9949, hc02, hc35, hlam, hphi, ht23]
                  · linarith only [h9896, h9946, h9948, hlam]
                · linarith only [h9779, h9894, h9946, h9947, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9983 | h9983
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9984 | h9984
                  · linarith only [h7594, h9896, h9945, h9946, h9984, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h7594, h9896, h9945, h9984, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h5743, h9894, h9983, hlam]
            · linarith only [h0, h9778, h9945, hlam]
      · linarith only [h8272, h9778, h9779, h9895, hlam]
    · linarith only [h8272, h9778, h9894, hlam]

end R2N4
