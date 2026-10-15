import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  rcases m.htr 1 2 3 (by decide) (by decide) with h36836 | h36836
  · rcases m.htr 1 2 4 (by decide) (by decide) with h36837 | h36837
    · rcases m.htr 1 2 5 (by decide) (by decide) with h36838 | h36838
      · rcases m.htr 1 3 4 (by decide) (by decide) with h36839 | h36839
        · rcases m.htr 1 3 5 (by decide) (by decide) with h36840 | h36840
          · rcases m.htr 1 4 5 (by decide) (by decide) with h36841 | h36841
            · rcases m.htr 2 3 4 (by decide) (by decide) with h36842 | h36842
              · rcases m.htr 2 3 5 (by decide) (by decide) with h36843 | h36843
                · rcases m.htr 2 4 5 (by decide) (by decide) with h36844 | h36844
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h36845 | h36845
                    · rcases h1bigk with h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c | h36846c
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h0, hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h33187, hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h33187, h36837, h36842, h36845, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p36846_1]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        rcases p36846_3 (m.d 0 1) (by simp) with h36851 | h36851
                        · rcases p36846_3 (m.d 1 2) (by simp) with h36852 | h36852
                          · rcases p36846_3 (m.d 1 3) (by simp) with h36853 | h36853
                            · rcases p36846_3 (m.d 1 4) (by simp) with h36854 | h36854
                              · linarith only [h36828, h36854, hlam]
                              · linarith only [h36841, h36854, hlam]
                            · linarith only [h36840, h36853, hlam]
                          · linarith only [h36838, h36852, hlam]
                        · linarith only [h36851, hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h36828, h36837, h36842, h36845, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p36846_1]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h33187, hc01, hc12, hlam, hphi, p36846_1]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        rcases p36846_3 (m.d 0 1) (by simp) with h36863 | h36863
                        · linarith only [h0, h36863, hlam]
                        · linarith only [h36828, h36863, hlam]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        rcases p36846_3 (m.d 0 1) (by simp) with h36866 | h36866
                        · linarith only [h0, h36866, hlam]
                        · linarith only [h36829, h36866, hlam]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h36828, h36837, h36842, h36845, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p36846_1]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h36836, hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        rcases p36846_3 (m.d 0 1) (by simp) with h36872 | h36872
                        · linarith only [h33187, h36872, hlam]
                        · linarith only [h36828, h36872, hlam]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        rcases p36846_3 (m.d 0 1) (by simp) with h36875 | h36875
                        · linarith only [h33187, h36875, hlam]
                        · linarith only [h36829, h36875, hlam]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h36828, hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h36837, hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h36839, hlam, p36846_1]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h0, h36828, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p36846_1]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h36829, hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h36838, hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h36840, hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [h36841, hlam, p36846_0]
                      · have p36846_0 := h36846c.1
                        have p36846_1 := h36846c.2.1
                        have p36846_2 := h36846c.2.2.1
                        have p36846_3 := h36846c.2.2.2
                        linarith only [hlam, p36846_0]
                    · linarith only [h33187, h36828, h36836, h36841, h36845, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h33187, h36828, h36836, h36841, h36844, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h33187, h36828, h36836, h36840, h36841, h36842, h36843, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h36891 | h36891
                · linarith only [h33187, h36828, h36836, h36839, h36842, h36891, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h36893 | h36893
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h36894 | h36894
                    · rcases h1bigk with h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c | h36895c
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h0, hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h33187, hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h33187, h36836, h36840, h36841, h36891, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p36895_1]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h33187, h36836, h36840, h36891, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p36895_1]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h36828, h36840, h36841, h36891, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p36895_1]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h33187, hc01, hc12, hlam, hphi, p36895_1]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        rcases p36895_3 (m.d 0 1) (by simp) with h36904 | h36904
                        · linarith only [h0, h36904, hlam]
                        · linarith only [h36828, h36904, hlam]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        rcases p36895_3 (m.d 0 1) (by simp) with h36907 | h36907
                        · linarith only [h0, h36907, hlam]
                        · linarith only [h36829, h36907, hlam]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h36828, h36840, h36841, h36891, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p36895_1]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h36836, hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        rcases p36895_3 (m.d 0 1) (by simp) with h36913 | h36913
                        · linarith only [h33187, h36913, hlam]
                        · linarith only [h36828, h36913, hlam]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        rcases p36895_3 (m.d 0 1) (by simp) with h36916 | h36916
                        · linarith only [h33187, h36916, hlam]
                        · linarith only [h36829, h36916, hlam]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h36828, hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h36837, hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h36839, hlam, p36895_1]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h36828, h36840, h36891, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p36895_1]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h36829, hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h36838, hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h36840, hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [h36841, hlam, p36895_0]
                      · have p36895_0 := h36895c.1
                        have p36895_1 := h36895c.2.1
                        have p36895_2 := h36895c.2.2.1
                        have p36895_3 := h36895c.2.2.2
                        linarith only [hlam, p36895_0]
                    · linarith only [h33187, h36828, h36836, h36837, h36893, h36894, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h33187, h36828, h36836, h36841, h36893, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h36931 | h36931
              · rcases m.htr 2 3 5 (by decide) (by decide) with h36932 | h36932
                · rcases m.htr 2 4 5 (by decide) (by decide) with h36933 | h36933
                  · linarith only [h36837, h36841, h36933, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h36935 | h36935
                    · linarith only [h36839, h36841, h36935, hlam]
                    · rcases h1bigk with h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c | h36937c
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h0, hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h33187, hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        rcases p36937_3 (m.d 0 1) (by simp) with h36941 | h36941
                        · rcases p36937_3 (m.d 1 2) (by simp) with h36942 | h36942
                          · rcases p36937_3 (m.d 1 3) (by simp) with h36943 | h36943
                            · rcases p36937_3 (m.d 1 4) (by simp) with h36944 | h36944
                              · linarith only [h36944, hlam, p36937_0]
                              · rcases p36937_3 (m.d 1 5) (by simp) with h36946 | h36946
                                · linarith only [h36829, h36946, hlam]
                                · linarith only [h36841, h36946, hlam]
                            · linarith only [h36839, h36943, hlam]
                          · linarith only [h36837, h36942, hlam]
                        · linarith only [h36941, hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        rcases p36937_3 (m.d 0 1) (by simp) with h36952 | h36952
                        · rcases p36937_3 (m.d 1 2) (by simp) with h36953 | h36953
                          · rcases p36937_3 (m.d 1 3) (by simp) with h36954 | h36954
                            · rcases p36937_3 (m.d 1 4) (by simp) with h36955 | h36955
                              · linarith only [h36828, h36955, hlam]
                              · rcases p36937_3 (m.d 1 5) (by simp) with h36957 | h36957
                                · linarith only [h36957, hlam, p36937_0]
                                · rcases h1emax with h36959 | h36959 | h36959 | h36959 | h36959
                                  · linarith only [h36959, hc15, hlam, hphi, ht01, ht0b, ht5b, p36937_1]
                                  · linarith only [h33187, h36828, h36835, h36836, h36837, h36841, h36931, h36959, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h33187, h36828, h36835, h36837, h36841, h36931, h36959, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h2bigk with h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c | h36963c
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h0, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      rcases p36963_3 (m.d 0 2) (by simp) with h36966 | h36966
                                      · rcases p36963_3 (m.d 1 2) (by simp) with h36967 | h36967
                                        · rcases p36963_3 (m.d 2 3) (by simp) with h36968 | h36968
                                          · linarith only [h36968, hlam, p36963_0]
                                          · rcases p36963_3 (m.d 2 4) (by simp) with h36970 | h36970
                                            · linarith only [h36831, h36970, hlam]
                                            · rcases p36963_3 (m.d 2 5) (by simp) with h36972 | h36972
                                              · linarith only [h36832, h36972, hlam]
                                              · rcases h4bigk with h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c | h36974c
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  rcases p36974_3 (m.d 0 4) (by simp) with h36976 | h36976
                                                  · rcases p36974_3 (m.d 1 4) (by simp) with h36977 | h36977
                                                    · linarith only [h36828, h36977, hlam]
                                                    · rcases p36974_3 (m.d 2 4) (by simp) with h36979 | h36979
                                                      · linarith only [h36831, h36979, hlam]
                                                      · rcases p36974_3 (m.d 3 4) (by simp) with h36981 | h36981
                                                        · linarith only [h36833, h36981, hlam]
                                                        · rcases p36974_3 (m.d 4 5) (by simp) with h36983 | h36983
                                                          · linarith only [h36835, h36983, hlam]
                                                          · linarith only [h36841, h36983, hlam]
                                                  · linarith only [h36828, h36976, hlam]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  rcases p36974_3 (m.d 0 4) (by simp) with h36987 | h36987
                                                  · rcases p36974_3 (m.d 1 4) (by simp) with h36988 | h36988
                                                    · linarith only [h36828, h36988, hlam]
                                                    · linarith only [h36837, h36988, hlam]
                                                  · linarith only [h36831, h36987, hlam]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  rcases p36974_3 (m.d 0 4) (by simp) with h36992 | h36992
                                                  · rcases p36974_3 (m.d 1 4) (by simp) with h36993 | h36993
                                                    · linarith only [h36828, h36993, hlam]
                                                    · linarith only [h36839, h36993, hlam]
                                                  · linarith only [h36833, h36992, hlam]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h33187, h36828, h36836, h36837, h36841, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36974_1]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h36828, hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h36841, h36931, hc34, hc45, hlam, hphi, p36974_1]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h33187, h36836, h36841, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36937_1, p36974_1]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h36841, hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h36831, hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h36837, hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h33187, h36836, h36837, h36841, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36937_1, p36974_1]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h36933, hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h36833, hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h36839, hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h36931, hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h36935, hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h36835, hlam, p36974_0]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h33187, h36828, h36835, h36836, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p36974_1]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h33187, h36828, h36835, h36836, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36974_1]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [h33187, h36828, h36835, h36836, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36974_1]
                                                · have p36974_0 := h36974c.1
                                                  have p36974_1 := h36974c.2.1
                                                  have p36974_2 := h36974c.2.2.1
                                                  have p36974_3 := h36974c.2.2.2
                                                  linarith only [hlam, p36974_0]
                                        · linarith only [h36836, h36967, hlam]
                                      · linarith only [h36966, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      rcases p36963_3 (m.d 0 2) (by simp) with h37020 | h37020
                                      · rcases p36963_3 (m.d 1 2) (by simp) with h37021 | h37021
                                        · rcases p36963_3 (m.d 2 3) (by simp) with h37022 | h37022
                                          · linarith only [h36830, h37022, hlam]
                                          · linarith only [h36931, h37022, hlam]
                                        · linarith only [h36837, h37021, hlam]
                                      · linarith only [h37020, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      rcases p36963_3 (m.d 0 2) (by simp) with h37027 | h37027
                                      · rcases p36963_3 (m.d 1 2) (by simp) with h37028 | h37028
                                        · rcases p36963_3 (m.d 2 3) (by simp) with h37029 | h37029
                                          · linarith only [h36830, h37029, hlam]
                                          · linarith only [h36932, h37029, hlam]
                                        · linarith only [h36838, h37028, hlam]
                                      · linarith only [h37027, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p36937_1, p36963_1]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      rcases p36963_3 (m.d 0 2) (by simp) with h37036 | h37036
                                      · linarith only [h0, h37036, hlam]
                                      · linarith only [h36830, h37036, hlam]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h0, h36838, h36933, hlam, p36937_1, p36963_2]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h33187, h36836, h36838, hlam, p36937_1, p36963_2]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h36830, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h36836, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      rcases p36963_3 (m.d 0 2) (by simp) with h37044 | h37044
                                      · rcases p36963_3 (m.d 1 2) (by simp) with h37045 | h37045
                                        · rcases p36963_3 (m.d 2 3) (by simp) with h37046 | h37046
                                          · rcases p36963_3 (m.d 2 4) (by simp) with h37047 | h37047
                                            · linarith only [h36931, h37047, hlam]
                                            · rcases p36963_3 (m.d 2 5) (by simp) with h37049 | h37049
                                              · linarith only [h36932, h37049, hlam]
                                              · linarith only [h36933, h37049, hlam]
                                          · linarith only [h36931, h37046, hlam]
                                        · linarith only [h36837, h37045, hlam]
                                      · linarith only [h36831, h37044, hlam]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      rcases p36963_3 (m.d 0 2) (by simp) with h37055 | h37055
                                      · rcases p36963_3 (m.d 1 2) (by simp) with h37056 | h37056
                                        · rcases p36963_3 (m.d 2 3) (by simp) with h37057 | h37057
                                          · rcases p36963_3 (m.d 2 4) (by simp) with h37058 | h37058
                                            · linarith only [h36931, h37058, hlam]
                                            · rcases p36963_3 (m.d 2 5) (by simp) with h37060 | h37060
                                              · linarith only [h36932, h37060, hlam]
                                              · rcases h4bigk with h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c | h37062c
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  rcases p37062_3 (m.d 0 4) (by simp) with h37064 | h37064
                                                  · rcases p37062_3 (m.d 1 4) (by simp) with h37065 | h37065
                                                    · linarith only [h36828, h37065, hlam]
                                                    · rcases p37062_3 (m.d 2 4) (by simp) with h37067 | h37067
                                                      · linarith only [h36831, h37067, hlam]
                                                      · rcases p37062_3 (m.d 3 4) (by simp) with h37069 | h37069
                                                        · linarith only [h36833, h37069, hlam]
                                                        · rcases p37062_3 (m.d 4 5) (by simp) with h37071 | h37071
                                                          · linarith only [h36835, h37071, hlam]
                                                          · linarith only [h36841, h37071, hlam]
                                                  · linarith only [h36828, h37064, hlam]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  rcases p37062_3 (m.d 0 4) (by simp) with h37075 | h37075
                                                  · rcases p37062_3 (m.d 1 4) (by simp) with h37076 | h37076
                                                    · linarith only [h36828, h37076, hlam]
                                                    · linarith only [h36837, h37076, hlam]
                                                  · linarith only [h36831, h37075, hlam]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  rcases p37062_3 (m.d 0 4) (by simp) with h37080 | h37080
                                                  · rcases p37062_3 (m.d 1 4) (by simp) with h37081 | h37081
                                                    · linarith only [h36828, h37081, hlam]
                                                    · linarith only [h36839, h37081, hlam]
                                                  · linarith only [h36833, h37080, hlam]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h33187, h36828, h36836, h36837, h36841, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37062_1]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h36828, hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h36841, h36931, hc34, hc45, hlam, hphi, p37062_1]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h33187, h36828, h36836, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37062_1]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h36841, hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h36831, hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h36837, hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h36933, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p36963_1, p37062_1]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h36933, hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h36833, hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h36839, hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h36931, hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h36935, hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h36835, hlam, p37062_0]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h33187, h36828, h36835, h36836, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37062_1]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h33187, h36828, h36835, h36836, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37062_1]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [h33187, h36828, h36835, h36836, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37062_1]
                                                · have p37062_0 := h37062c.1
                                                  have p37062_1 := h37062c.2.1
                                                  have p37062_2 := h37062c.2.2.1
                                                  have p37062_3 := h37062c.2.2.2
                                                  linarith only [hlam, p37062_0]
                                          · linarith only [h36932, h37057, hlam]
                                        · linarith only [h36838, h37056, hlam]
                                      · linarith only [h36832, h37055, hlam]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h36831, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h36837, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h36931, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h36933, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h36832, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h36838, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h36932, hlam, p36963_0]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [h33187, h36836, h36838, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36937_1, p36963_1]
                                    · have p36963_0 := h36963c.1
                                      have p36963_1 := h36963c.2.1
                                      have p36963_2 := h36963c.2.2.1
                                      have p36963_3 := h36963c.2.2.2
                                      linarith only [hlam, p36963_0]
                                  · rcases h2bigk with h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c | h37119c
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h0, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      rcases p37119_3 (m.d 0 2) (by simp) with h37122 | h37122
                                      · rcases p37119_3 (m.d 1 2) (by simp) with h37123 | h37123
                                        · rcases p37119_3 (m.d 2 3) (by simp) with h37124 | h37124
                                          · linarith only [h37124, hlam, p37119_0]
                                          · rcases p37119_3 (m.d 2 4) (by simp) with h37126 | h37126
                                            · linarith only [h36831, h37126, hlam]
                                            · rcases p37119_3 (m.d 2 5) (by simp) with h37128 | h37128
                                              · linarith only [h36832, h37128, hlam]
                                              · rcases h4bigk with h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c | h37130c
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  rcases p37130_3 (m.d 0 4) (by simp) with h37132 | h37132
                                                  · rcases p37130_3 (m.d 1 4) (by simp) with h37133 | h37133
                                                    · linarith only [h36828, h37133, hlam]
                                                    · rcases p37130_3 (m.d 2 4) (by simp) with h37135 | h37135
                                                      · linarith only [h36831, h37135, hlam]
                                                      · rcases p37130_3 (m.d 3 4) (by simp) with h37137 | h37137
                                                        · linarith only [h36833, h37137, hlam]
                                                        · rcases p37130_3 (m.d 4 5) (by simp) with h37139 | h37139
                                                          · linarith only [h36835, h37139, hlam]
                                                          · linarith only [h36841, h37139, hlam]
                                                  · linarith only [h36828, h37132, hlam]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  rcases p37130_3 (m.d 0 4) (by simp) with h37143 | h37143
                                                  · rcases p37130_3 (m.d 1 4) (by simp) with h37144 | h37144
                                                    · linarith only [h36828, h37144, hlam]
                                                    · linarith only [h36837, h37144, hlam]
                                                  · linarith only [h36831, h37143, hlam]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  rcases p37130_3 (m.d 0 4) (by simp) with h37148 | h37148
                                                  · rcases p37130_3 (m.d 1 4) (by simp) with h37149 | h37149
                                                    · linarith only [h36828, h37149, hlam]
                                                    · linarith only [h36839, h37149, hlam]
                                                  · linarith only [h36833, h37148, hlam]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h33187, h36828, h36836, h36837, h36841, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37130_1]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h36828, hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h33187, h36828, h36836, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37130_1]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h33187, h36828, h36836, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37130_1]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h36841, hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h36831, hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h36837, hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h33187, h36828, h36836, h36837, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37130_1]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h36933, hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h36833, hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h36839, hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h36931, hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h36935, hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h36835, hlam, p37130_0]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h33187, h36828, h36835, h36836, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37130_1]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h33187, h36828, h36835, h36836, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37130_1]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [h33187, h36828, h36835, h36836, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37130_1]
                                                · have p37130_0 := h37130c.1
                                                  have p37130_1 := h37130c.2.1
                                                  have p37130_2 := h37130c.2.2.1
                                                  have p37130_3 := h37130c.2.2.2
                                                  linarith only [hlam, p37130_0]
                                        · linarith only [h36836, h37123, hlam]
                                      · linarith only [h37122, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      rcases p37119_3 (m.d 0 2) (by simp) with h37176 | h37176
                                      · rcases p37119_3 (m.d 1 2) (by simp) with h37177 | h37177
                                        · rcases p37119_3 (m.d 2 3) (by simp) with h37178 | h37178
                                          · linarith only [h36830, h37178, hlam]
                                          · linarith only [h36931, h37178, hlam]
                                        · linarith only [h36837, h37177, hlam]
                                      · linarith only [h37176, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      rcases p37119_3 (m.d 0 2) (by simp) with h37183 | h37183
                                      · rcases p37119_3 (m.d 1 2) (by simp) with h37184 | h37184
                                        · rcases p37119_3 (m.d 2 3) (by simp) with h37185 | h37185
                                          · linarith only [h36830, h37185, hlam]
                                          · linarith only [h36932, h37185, hlam]
                                        · linarith only [h36838, h37184, hlam]
                                      · linarith only [h37183, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h0, h36828, h36835, h36841, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37119_1]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      rcases p37119_3 (m.d 0 2) (by simp) with h37192 | h37192
                                      · linarith only [h0, h37192, hlam]
                                      · linarith only [h36830, h37192, hlam]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h0, h36828, h36835, h36837, h36841, hlam, p37119_2]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h33187, h36836, h36838, hlam, p36937_1, p37119_2]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h36830, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h36836, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      rcases p37119_3 (m.d 0 2) (by simp) with h37200 | h37200
                                      · rcases p37119_3 (m.d 1 2) (by simp) with h37201 | h37201
                                        · rcases p37119_3 (m.d 2 3) (by simp) with h37202 | h37202
                                          · rcases p37119_3 (m.d 2 4) (by simp) with h37203 | h37203
                                            · linarith only [h36931, h37203, hlam]
                                            · rcases p37119_3 (m.d 2 5) (by simp) with h37205 | h37205
                                              · linarith only [h36932, h37205, hlam]
                                              · linarith only [h36933, h37205, hlam]
                                          · linarith only [h36931, h37202, hlam]
                                        · linarith only [h36837, h37201, hlam]
                                      · linarith only [h36831, h37200, hlam]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      rcases p37119_3 (m.d 0 2) (by simp) with h37211 | h37211
                                      · rcases p37119_3 (m.d 1 2) (by simp) with h37212 | h37212
                                        · rcases p37119_3 (m.d 2 3) (by simp) with h37213 | h37213
                                          · rcases p37119_3 (m.d 2 4) (by simp) with h37214 | h37214
                                            · linarith only [h36931, h37214, hlam]
                                            · rcases p37119_3 (m.d 2 5) (by simp) with h37216 | h37216
                                              · linarith only [h36932, h37216, hlam]
                                              · rcases h4bigk with h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c | h37218c
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  rcases p37218_3 (m.d 0 4) (by simp) with h37220 | h37220
                                                  · rcases p37218_3 (m.d 1 4) (by simp) with h37221 | h37221
                                                    · linarith only [h36828, h37221, hlam]
                                                    · rcases p37218_3 (m.d 2 4) (by simp) with h37223 | h37223
                                                      · linarith only [h36831, h37223, hlam]
                                                      · rcases p37218_3 (m.d 3 4) (by simp) with h37225 | h37225
                                                        · linarith only [h36833, h37225, hlam]
                                                        · rcases p37218_3 (m.d 4 5) (by simp) with h37227 | h37227
                                                          · linarith only [h36835, h37227, hlam]
                                                          · linarith only [h36841, h37227, hlam]
                                                  · linarith only [h36828, h37220, hlam]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  rcases p37218_3 (m.d 0 4) (by simp) with h37231 | h37231
                                                  · rcases p37218_3 (m.d 1 4) (by simp) with h37232 | h37232
                                                    · linarith only [h36828, h37232, hlam]
                                                    · linarith only [h36837, h37232, hlam]
                                                  · linarith only [h36831, h37231, hlam]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  rcases p37218_3 (m.d 0 4) (by simp) with h37236 | h37236
                                                  · rcases p37218_3 (m.d 1 4) (by simp) with h37237 | h37237
                                                    · linarith only [h36828, h37237, hlam]
                                                    · linarith only [h36839, h37237, hlam]
                                                  · linarith only [h36833, h37236, hlam]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h33187, h36828, h36836, h36837, h36841, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37218_1]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h36828, hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h36841, h36931, hc34, hc45, hlam, hphi, p37218_1]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h33187, h36828, h36836, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37218_1]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h36841, hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h36831, hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h36837, hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h33187, h36828, h36836, h36837, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37218_1]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h36933, hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h36833, hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h36839, hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h36931, hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h36935, hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h36835, hlam, p37218_0]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h33187, h36828, h36835, h36836, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37218_1]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h33187, h36828, h36835, h36836, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37218_1]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [h33187, h36828, h36835, h36836, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37218_1]
                                                · have p37218_0 := h37218c.1
                                                  have p37218_1 := h37218c.2.1
                                                  have p37218_2 := h37218c.2.2.1
                                                  have p37218_3 := h37218c.2.2.2
                                                  linarith only [hlam, p37218_0]
                                          · linarith only [h36932, h37213, hlam]
                                        · linarith only [h36838, h37212, hlam]
                                      · linarith only [h36832, h37211, hlam]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h36831, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h36837, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h36931, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h36933, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h36832, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h36838, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h36932, hlam, p37119_0]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [h33187, h36836, h36838, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36937_1, p37119_1]
                                    · have p37119_0 := h37119c.1
                                      have p37119_1 := h37119c.2.1
                                      have p37119_2 := h37119c.2.2.1
                                      have p37119_3 := h37119c.2.2.2
                                      linarith only [hlam, p37119_0]
                            · linarith only [h36840, h36954, hlam]
                          · linarith only [h36838, h36953, hlam]
                        · linarith only [h36952, hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h36828, h36835, h36837, h36841, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36937_1]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h33187, hc01, hc12, hlam, hphi, p36937_1]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h0, h36828, h36835, h36841, hlam, p36937_2]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        rcases p36937_3 (m.d 0 1) (by simp) with h37282 | h37282
                        · linarith only [h0, h37282, hlam]
                        · linarith only [h36829, h37282, hlam]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h36828, h36835, h36836, h36837, h36841, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36937_1]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h36836, hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h33187, h36828, h36835, h36841, hlam, p36937_2]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        rcases p36937_3 (m.d 0 1) (by simp) with h37289 | h37289
                        · linarith only [h33187, h37289, hlam]
                        · linarith only [h36829, h37289, hlam]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h36828, hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h36837, hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h36839, hlam, p36937_1]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h36841, hlam, p36937_1]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h36829, hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h36838, hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h36840, hlam, p36937_0]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [h0, h36829, h36837, h36931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36937_1]
                      · have p36937_0 := h36937c.1
                        have p36937_1 := h36937c.2.1
                        have p36937_2 := h36937c.2.2.1
                        have p36937_3 := h36937c.2.2.2
                        linarith only [hlam, p36937_0]
                · linarith only [h33187, h36828, h36835, h36836, h36840, h36841, h36931, h36932, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h33187, h36828, h36835, h36836, h36839, h36841, h36931, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h33187, h36830, h36834, h36840, hc01, hc12, hlam, hphi]
        · linarith only [h33187, h36828, h36833, h36839, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h0, h36832, h36838, hlam]
    · linarith only [h0, h36831, h36837, hlam]
  · linarith only [h0, h36830, h36836, hlam]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  linarith only [h36828, h36835, h37314, hlam]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  linarith only [h36828, h36835, h37310, h37318, hlam]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  linarith only [h36828, h36835, h37310, h37316, h37320, hlam]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 0 1) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 1) ∧ (m.d 0 1) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 0 1) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  linarith only [hlam, p37322_0]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 0 1) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 0 1) ∧ (m.d 1 2) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 2) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  linarith only [h0, hlam, p37322_0]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 0 1) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 0 1) ∧ (m.d 1 3) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 3) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  linarith only [h33187, hlam, p37322_0]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 0 1) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 0 1) ∧ (m.d 1 4) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 4) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  rcases p37322_3 (m.d 0 1) (by simp) with h37326 | h37326
  · rcases p37322_3 (m.d 1 2) (by simp) with h37327 | h37327
    · rcases p37322_3 (m.d 1 3) (by simp) with h37328 | h37328
      · rcases p37322_3 (m.d 1 4) (by simp) with h37329 | h37329
        · linarith only [h37329, hlam, p37322_0]
        · rcases p37322_3 (m.d 1 5) (by simp) with h37331 | h37331
          · linarith only [h36829, h37331, hlam]
          · linarith only [h37314, h37331, hlam]
      · linarith only [h37312, h37328, hlam]
    · linarith only [h37310, h37327, hlam]
  · linarith only [h37326, hlam, p37322_0]

end R2N4
