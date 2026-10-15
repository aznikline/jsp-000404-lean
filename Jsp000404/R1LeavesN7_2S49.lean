import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S48

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16917 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 0 2 4 (by decide) (by decide) with h16918 | h16918
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916 h16917 h16918
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916 h16917 h16918

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16917 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 0 2 4 (by decide) (by decide) with h17780 | h17780
  · rcases m.htr 0 2 5 (by decide) (by decide) with h17781 | h17781
    · rcases m.htr 0 3 4 (by decide) (by decide) with h17782 | h17782
      · rcases m.htr 0 3 5 (by decide) (by decide) with h17783 | h17783
        · rcases m.htr 0 4 5 (by decide) (by decide) with h17784 | h17784
          · rcases m.htr 1 2 3 (by decide) (by decide) with h17785 | h17785
            · rcases m.htr 1 2 4 (by decide) (by decide) with h17786 | h17786
              · rcases m.htr 1 2 5 (by decide) (by decide) with h17787 | h17787
                · rcases m.htr 1 3 4 (by decide) (by decide) with h17788 | h17788
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h17789 | h17789
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h17790 | h17790
                      · linarith only [h0, h16915, h16917, h17785, h17790, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h16915, h16917, h17784, h17785, h17790, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h14396, h16915, h17783, h17784, h17789, hc03, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h14396, h17782, h17788, hlam]
                · linarith only [h16917, h17785, h17787, hc02, hc25, hlam, hphi]
              · linarith only [h16917, h17785, h17786, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h17797 | h17797
              · rcases m.htr 1 2 5 (by decide) (by decide) with h17798 | h17798
                · rcases m.htr 1 3 4 (by decide) (by decide) with h17799 | h17799
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h17800 | h17800
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h17801 | h17801
                      · linarith only [h0, h16915, h17785, h17801, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h16915, h17784, h17785, h17797, h17801, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h16915, h17783, h17784, h17785, h17800, hc03, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h14396, h17782, h17799, hlam]
                · linarith only [h0, h16915, h17781, h17797, h17798, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h16915, h17780, h17797, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h17808 | h17808
            · rcases m.htr 1 2 4 (by decide) (by decide) with h17809 | h17809
              · rcases m.htr 1 2 5 (by decide) (by decide) with h17810 | h17810
                · rcases m.htr 1 3 4 (by decide) (by decide) with h17811 | h17811
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h17812 | h17812
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h17813 | h17813
                      · linarith only [h16915, h17784, h17813, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h17815 | h17815
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h17816 | h17816
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h17817 | h17817
                            · linarith only [h16915, h17784, h17809, h17817, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h17819 | h17819
                              · linarith only [h16915, h17784, h17809, h17815, h17819, hlam]
                              · rcases h0bigk with h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c | h17821c
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [hlam, p17821_0]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h0, hlam, p17821_1]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h14396, hlam, p17821_0]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h0, h16917, h17808, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p17821_1]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h0, h16915, h16917, h17784, h17808, h17809, h17815, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17821_1]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h16917, h17808, hc01, hc12, hlam, hphi, p17821_1]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [hlam, p17821_0]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h16917, hlam, p17821_0]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h16915, h16917, h17808, h17809, h17815, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17821_1]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h16915, h16917, h17784, h17808, h17809, h17815, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17821_1]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h16915, h16917, h17808, h17809, h17815, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17821_1]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h0, h16915, h16917, h17808, h17809, h17815, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17821_1]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [hlam, p17821_0]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  rcases p17821_3 (m.d 0 1) (by simp) with h17835 | h17835
                                  · linarith only [h14396, h17835, hlam]
                                  · linarith only [h16915, h17835, hlam]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  rcases p17821_3 (m.d 0 1) (by simp) with h17838 | h17838
                                  · linarith only [h14396, h17838, hlam]
                                  · linarith only [h16916, h17838, hlam]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h16915, hlam, p17821_0]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h17780, hlam, p17821_0]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h17782, hlam, p17821_0]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [hlam, p17821_0]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h17784, hlam, p17821_0]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h16916, hlam, p17821_0]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h17781, hlam, p17821_1]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h17783, hlam, p17821_0]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [h0, h16915, h16916, h16917, h17808, h17809, h17815, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17821_1]
                                · have p17821_0 := h17821c.1
                                  have p17821_1 := h17821c.2.1
                                  have p17821_2 := h17821c.2.2.1
                                  have p17821_3 := h17821c.2.2.2
                                  linarith only [hlam, p17821_0]
                          · linarith only [h16917, h17783, h17816, hlam]
                        · linarith only [h16917, h17782, h17815, hlam]
                    · linarith only [h14396, h16917, h17783, h17812, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h16917, h17782, h17808, h17811, hlam]
                · linarith only [h16917, h17781, h17810, hc12, hc23, hlam, hphi]
              · linarith only [h0, h16915, h16917, h17780, h17808, h17809, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h17857 | h17857
              · rcases m.htr 1 2 5 (by decide) (by decide) with h17858 | h17858
                · rcases m.htr 1 3 4 (by decide) (by decide) with h17859 | h17859
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h17860 | h17860
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h17861 | h17861
                      · linarith only [h0, h16915, h17808, h17861, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h17863 | h17863
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h17864 | h17864
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h17865 | h17865
                            · linarith only [h0, h16915, h17784, h17808, h17857, h17865, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h17867 | h17867
                              · linarith only [h0, h16915, h17784, h17808, h17857, h17863, h17867, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases h0bigk with h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c | h17869c
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [hlam, p17869_0]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h0, hlam, p17869_1]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h14396, hlam, p17869_0]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h0, h16915, h17808, h17857, h17863, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17869_1]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h0, h17808, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p17869_1]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h0, h17808, hc01, hc23, hlam, hphi, ht12, p17869_1]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [hlam, p17869_0]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h16917, hlam, p17869_0]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  rcases p17869_3 (m.d 0 1) (by simp) with h17878 | h17878
                                  · linarith only [h0, h17878, hlam]
                                  · linarith only [h16915, h17878, hlam]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  rcases p17869_3 (m.d 0 1) (by simp) with h17881 | h17881
                                  · linarith only [h0, h17881, hlam]
                                  · linarith only [h16916, h17881, hlam]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  rcases p17869_3 (m.d 0 1) (by simp) with h17884 | h17884
                                  · linarith only [h14396, h17884, hlam]
                                  · rcases p17869_3 (m.d 0 2) (by simp) with h17886 | h17886
                                    · linarith only [h16917, h17886, hlam]
                                    · linarith only [h0, h17886, hlam]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  rcases p17869_3 (m.d 0 1) (by simp) with h17889 | h17889
                                  · linarith only [h14396, h17889, hlam]
                                  · rcases p17869_3 (m.d 0 2) (by simp) with h17891 | h17891
                                    · linarith only [h16917, h17891, hlam]
                                    · rcases p17869_3 (m.d 0 3) (by simp) with h17893 | h17893
                                      · rcases p17869_3 (m.d 0 4) (by simp) with h17894 | h17894
                                        · linarith only [h17782, h17894, hlam]
                                        · rcases p17869_3 (m.d 0 5) (by simp) with h17896 | h17896
                                          · linarith only [h17783, h17896, hlam]
                                          · rcases h2bigk with h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c | h17898c
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [hlam, p17898_0]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h0, hlam, p17898_1]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h16917, hlam, p17898_0]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h14396, h17808, h17863, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17869_1, p17898_1]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h14396, h17808, h17863, h17865, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17869_1, p17898_1]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h17808, hc02, hc23, hlam, hphi, p17898_1]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [hlam, p17898_0]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h17808, hlam, p17898_0]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              rcases p17898_3 (m.d 0 2) (by simp) with h17907 | h17907
                                              · linarith only [h0, h17907, hlam]
                                              · linarith only [h17780, h17907, hlam]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              rcases p17898_3 (m.d 0 2) (by simp) with h17910 | h17910
                                              · linarith only [h0, h17910, hlam]
                                              · linarith only [h17781, h17910, hlam]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              rcases p17898_3 (m.d 0 2) (by simp) with h17913 | h17913
                                              · linarith only [h17913, hlam, p17898_0]
                                              · rcases p17898_3 (m.d 1 2) (by simp) with h17915 | h17915
                                                · linarith only [h17808, h17915, hlam]
                                                · linarith only [h0, h17915, hlam]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h0, h16916, h17857, h17861, h17863, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17898_1]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [hlam, p17898_0]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h0, h14396, h16916, h17808, h17857, h17861, hlam, p17869_1, p17898_2]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h14396, h17781, h17808, hlam, p17869_1, p17898_2]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h17780, hlam, p17898_0]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h17857, hlam, p17898_0]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h17863, hlam, p17898_1]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [hlam, p17898_0]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h17865, hlam, p17898_1]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h17781, hlam, p17898_0]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h17858, hlam, p17898_0]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h17864, hlam, p17898_1]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [h0, h16916, h17858, h17863, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p17869_1, p17898_1]
                                            · have p17898_0 := h17898c.1
                                              have p17898_1 := h17898c.2.1
                                              have p17898_2 := h17898c.2.2.1
                                              have p17898_3 := h17898c.2.2.2
                                              linarith only [hlam, p17898_0]
                                      · linarith only [h16917, h17893, hlam]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [hlam, p17869_0]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  rcases p17869_3 (m.d 0 1) (by simp) with h17934 | h17934
                                  · linarith only [h14396, h17934, hlam]
                                  · linarith only [h16915, h17934, hlam]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  rcases p17869_3 (m.d 0 1) (by simp) with h17937 | h17937
                                  · linarith only [h14396, h17937, hlam]
                                  · linarith only [h16916, h17937, hlam]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h16915, hlam, p17869_0]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h17780, hlam, p17869_0]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h17782, hlam, p17869_0]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [hlam, p17869_0]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h17784, hlam, p17869_0]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h16916, hlam, p17869_0]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h17781, hlam, p17869_1]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h17783, hlam, p17869_0]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [h0, h16915, h16916, h17808, h17857, h17863, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17869_1]
                                · have p17869_0 := h17869c.1
                                  have p17869_1 := h17869c.2.1
                                  have p17869_2 := h17869c.2.2.1
                                  have p17869_3 := h17869c.2.2.2
                                  linarith only [hlam, p17869_0]
                          · linarith only [h0, h17808, h17864, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h14396, h17782, h17808, h17863, hlam]
                    · linarith only [h14396, h17783, h17860, hlam]
                  · linarith only [h14396, h16916, h17782, h17859, hc03, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h16915, h17781, h17857, h17858, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h17780, h17857, hlam]
        · linarith only [h0, h16916, h16917, h17783, hlam]
      · linarith only [h0, h16915, h16917, h17782, hlam]
    · linarith only [h0, h16916, h17781, hlam]
  · linarith only [h0, h16915, h17780, hlam]

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 0 2 3 (by decide) (by decide) with h16917 | h16917
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916 h16917
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916 h16917

end R2N4
