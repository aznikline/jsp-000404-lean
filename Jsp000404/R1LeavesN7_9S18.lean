import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h13831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 3 4 (by decide) (by decide) with h13832 | h13832
  · rcases m.htr 0 3 5 (by decide) (by decide) with h13833 | h13833
    · rcases m.htr 0 4 5 (by decide) (by decide) with h13834 | h13834
      · rcases m.htr 1 2 3 (by decide) (by decide) with h13835 | h13835
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13836 | h13836
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13837 | h13837
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13838 | h13838
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13839 | h13839
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13840 | h13840
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13841 | h13841
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13842 | h13842
                      · linarith only [h11548, h13831, h13835, h13842, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h11548, h13831, h13834, h13835, h13842, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h11548, h13831, h13833, h13834, h13841, hc03, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h11548, h13832, h13840, hlam]
                · linarith only [h11548, h13831, h13834, h13839, h8811, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h11548, h13831, h13833, h13834, h13835, h13838, h7360, hc01, hc12, hlam, hphi]
            · linarith only [h11548, h13831, h13832, h13835, h13837, hlam]
          · linarith only [h11548, h13831, h13835, h13836, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13851 | h13851
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13852 | h13852
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13853 | h13853
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13854 | h13854
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13855 | h13855
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13856 | h13856
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13857 | h13857
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13858 | h13858
                        · rcases h3bigk with h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c | h13859c
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h7360, hlam, p13859_1]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h11548, hlam, p13859_1]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            rcases p13859_3 (m.d 0 3) (by simp) with h13863 | h13863
                            · rcases p13859_3 (m.d 1 3) (by simp) with h13864 | h13864
                              · rcases p13859_3 (m.d 2 3) (by simp) with h13865 | h13865
                                · rcases p13859_3 (m.d 3 4) (by simp) with h13866 | h13866
                                  · linarith only [h13866, hlam, p13859_0]
                                  · rcases p13859_3 (m.d 3 5) (by simp) with h13868 | h13868
                                    · linarith only [h13833, h13868, hlam]
                                    · rcases h4bigk with h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c | h13870c
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [hlam, p13870_0]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h8811, hlam, p13870_0]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13831, h13855, h13858, hc02, hc45, hlam, hphi, ht0b, ht5b, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h0, h13831, h13835, h13858, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h0, h13831, h13835, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h8811, hc01, hc14, hlam, hphi, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [hlam, p13870_0]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13835, h13851, h13855, h13858, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13835, h13851, h13858, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13835, h13851, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13831, hlam, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13851, hlam, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [hlam, p13870_0]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13831, h13858, hc04, hc45, hlam, hphi, ht0b, ht5b, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h0, h13831, h13835, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13832, hlam, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13852, hlam, p13870_0]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13855, hlam, p13870_0]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [hlam, p13870_0]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13835, h7360, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13859_1, p13870_1]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13834, hlam, p13870_0]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13854, hlam, p13870_0]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13857, hlam, p13870_0]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [h13858, hlam, p13870_0]
                                      · have p13870_0 := h13870c.1
                                        have p13870_1 := h13870c.2.1
                                        have p13870_2 := h13870c.2.2.1
                                        have p13870_3 := h13870c.2.2.2
                                        linarith only [hlam, p13870_0]
                                · linarith only [h13855, h13865, hlam]
                              · linarith only [h13852, h13864, hlam]
                            · linarith only [h13863, hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            rcases p13859_3 (m.d 0 3) (by simp) with h13899 | h13899
                            · rcases p13859_3 (m.d 1 3) (by simp) with h13900 | h13900
                              · rcases p13859_3 (m.d 2 3) (by simp) with h13901 | h13901
                                · rcases p13859_3 (m.d 3 4) (by simp) with h13902 | h13902
                                  · linarith only [h13832, h13902, hlam]
                                  · linarith only [h13858, h13902, hlam]
                                · linarith only [h13856, h13901, hlam]
                              · linarith only [h13853, h13900, hlam]
                            · linarith only [h13899, hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h11548, h13831, h13835, h13857, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13859_1]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h13835, hlam, p13859_1]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            rcases p13859_3 (m.d 0 3) (by simp) with h13911 | h13911
                            · linarith only [h13911, h7360, hlam]
                            · linarith only [h13832, h13911, hlam]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            rcases p13859_3 (m.d 0 3) (by simp) with h13914 | h13914
                            · linarith only [h13914, h7360, hlam]
                            · linarith only [h13833, h13914, hlam]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h11548, h13831, h13855, h13858, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13859_1]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h7360, hc01, hc23, hlam, hphi, ht12, p13859_1]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            rcases p13859_3 (m.d 0 3) (by simp) with h13920 | h13920
                            · linarith only [h11548, h13920, hlam]
                            · linarith only [h13832, h13920, hlam]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            rcases p13859_3 (m.d 0 3) (by simp) with h13923 | h13923
                            · linarith only [h11548, h13923, hlam]
                            · linarith only [h13833, h13923, hlam]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h13832, hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h13852, hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h13855, hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h0, h13831, h13835, h13855, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p13859_1]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h13833, hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h13853, hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h13856, hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [h13858, hlam, p13859_0]
                          · have p13859_0 := h13859c.1
                            have p13859_1 := h13859c.2.1
                            have p13859_2 := h13859c.2.2.1
                            have p13859_3 := h13859c.2.2.2
                            linarith only [hlam, p13859_0]
                        · linarith only [h0, h13831, h13835, h13857, h13858, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13937 | h13937
                        · linarith only [h13855, h13857, h13937, hlam]
                        · rcases h3bigk with h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c | h13939c
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [hlam, p13939_0]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h7360, hlam, p13939_1]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h11548, hlam, p13939_1]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            rcases p13939_3 (m.d 0 3) (by simp) with h13943 | h13943
                            · rcases p13939_3 (m.d 1 3) (by simp) with h13944 | h13944
                              · rcases p13939_3 (m.d 2 3) (by simp) with h13945 | h13945
                                · rcases p13939_3 (m.d 3 4) (by simp) with h13946 | h13946
                                  · linarith only [h13946, hlam, p13939_0]
                                  · rcases p13939_3 (m.d 3 5) (by simp) with h13948 | h13948
                                    · linarith only [h13833, h13948, hlam]
                                    · linarith only [h13937, h13948, hlam]
                                · linarith only [h13855, h13945, hlam]
                              · linarith only [h13852, h13944, hlam]
                            · linarith only [h13943, hlam, p13939_0]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            rcases p13939_3 (m.d 0 3) (by simp) with h13954 | h13954
                            · rcases p13939_3 (m.d 1 3) (by simp) with h13955 | h13955
                              · rcases p13939_3 (m.d 2 3) (by simp) with h13956 | h13956
                                · rcases p13939_3 (m.d 3 4) (by simp) with h13957 | h13957
                                  · linarith only [h13832, h13957, hlam]
                                  · rcases p13939_3 (m.d 3 5) (by simp) with h13959 | h13959
                                    · linarith only [h13959, hlam, p13939_0]
                                    · rcases h4bigk with h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c | h13961c
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [hlam, p13961_0]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h8811, hlam, p13961_0]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h0, h13831, h13835, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h0, h13831, h13835, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h0, h13831, h13835, h13857, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13835, h13851, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [hlam, p13961_0]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13835, h13851, h13855, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13835, h13851, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13835, h13851, h13857, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13831, hlam, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13851, hlam, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [hlam, p13961_0]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h0, h13831, h13835, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13857, hlam, p13961_0]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13832, hlam, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13852, hlam, p13961_0]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13855, hlam, p13961_0]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [hlam, p13961_0]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13937, hlam, p13961_0]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13834, hlam, p13961_0]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13854, hlam, p13961_0]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [hc24, hc45, hlam, hphi, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [h13834, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p13961_1]
                                      · have p13961_0 := h13961c.1
                                        have p13961_1 := h13961c.2.1
                                        have p13961_2 := h13961c.2.2.1
                                        have p13961_3 := h13961c.2.2.2
                                        linarith only [hlam, p13961_0]
                                · linarith only [h13856, h13956, hlam]
                              · linarith only [h13853, h13955, hlam]
                            · linarith only [h13954, hlam, p13939_0]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h11548, h13831, h13834, h13835, h13855, h13857, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13939_1]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [hlam, p13939_0]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h13835, hlam, p13939_1]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            rcases p13939_3 (m.d 0 3) (by simp) with h13993 | h13993
                            · linarith only [h13993, h7360, hlam]
                            · linarith only [h13832, h13993, hlam]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            rcases p13939_3 (m.d 0 3) (by simp) with h13996 | h13996
                            · linarith only [h13996, h7360, hlam]
                            · linarith only [h13833, h13996, hlam]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h11548, h13831, h13834, h13857, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13939_1]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h7360, hc01, hc23, hlam, hphi, ht12, p13939_1]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [hlam, p13939_0]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h0, h13831, h13834, h13835, h13855, h13857, hlam, p13939_2]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            rcases p13939_3 (m.d 0 3) (by simp) with h14003 | h14003
                            · linarith only [h11548, h14003, hlam]
                            · linarith only [h13833, h14003, hlam]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h13832, hlam, p13939_0]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h13852, hlam, p13939_0]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h13855, hlam, p13939_0]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [hlam, p13939_0]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h13937, hlam, p13939_1]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h13833, hlam, p13939_0]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h13853, hlam, p13939_0]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h13856, hlam, p13939_0]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [h0, h13831, h13834, h13835, h13856, h13857, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13939_1]
                          · have p13939_0 := h13939c.1
                            have p13939_1 := h13939c.2.1
                            have p13939_2 := h13939c.2.2.1
                            have p13939_3 := h13939c.2.2.2
                            linarith only [hlam, p13939_0]
                    · linarith only [h0, h13831, h13833, h13834, h13835, h13856, h7360, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h13832, h13835, h13855, h7360, hlam]
                · linarith only [h0, h13831, h13834, h13854, h8811, hc01, hc12, hlam, hphi]
              · linarith only [h0, h13831, h13833, h13834, h13835, h13853, h7360, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h13832, h13852, h7360, hlam]
          · linarith only [h0, h13831, h13851, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h14022 | h14022
        · rcases m.htr 1 2 4 (by decide) (by decide) with h14023 | h14023
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14024 | h14024
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14025 | h14025
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14026 | h14026
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14027 | h14027
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14028 | h14028
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14029 | h14029
                      · linarith only [h11548, h13831, h13834, h14029, h7360, h8811, hc01, hc13, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14031 | h14031
                        · linarith only [h11548, h13831, h13834, h14022, h14027, h14031, h8811, hc01, hc12, hlam, hphi]
                        · rcases h3bigk with h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c | h14033c
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h7360, hlam, p14033_1]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h11548, hlam, p14033_1]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            rcases p14033_3 (m.d 0 3) (by simp) with h14037 | h14037
                            · rcases p14033_3 (m.d 1 3) (by simp) with h14038 | h14038
                              · rcases p14033_3 (m.d 2 3) (by simp) with h14039 | h14039
                                · rcases p14033_3 (m.d 3 4) (by simp) with h14040 | h14040
                                  · linarith only [h14040, hlam, p14033_0]
                                  · rcases p14033_3 (m.d 3 5) (by simp) with h14042 | h14042
                                    · linarith only [h13833, h14042, hlam]
                                    · linarith only [h14031, h14042, hlam]
                                · linarith only [h14027, h14039, hlam]
                              · linarith only [h14024, h14038, hlam]
                            · linarith only [h14037, hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            rcases p14033_3 (m.d 0 3) (by simp) with h14048 | h14048
                            · rcases p14033_3 (m.d 1 3) (by simp) with h14049 | h14049
                              · rcases p14033_3 (m.d 2 3) (by simp) with h14050 | h14050
                                · rcases p14033_3 (m.d 3 4) (by simp) with h14051 | h14051
                                  · linarith only [h13832, h14051, hlam]
                                  · rcases p14033_3 (m.d 3 5) (by simp) with h14053 | h14053
                                    · linarith only [h14053, hlam, p14033_0]
                                    · rcases h4bigk with h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c | h14055c
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [hlam, p14055_0]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h8811, hlam, p14055_0]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h13834, h14026, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p14055_1]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h11548, h13831, h14022, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14055_1]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h13834, hlam, p14055_0]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h8811, hc01, hc14, hlam, hphi, p14055_1]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [hlam, p14055_0]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        rcases p14055_3 (m.d 0 4) (by simp) with h14063 | h14063
                                        · linarith only [h14063, h8811, hlam]
                                        · linarith only [h13831, h14063, hlam]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        rcases p14055_3 (m.d 0 4) (by simp) with h14066 | h14066
                                        · linarith only [h14066, h8811, hlam]
                                        · linarith only [h13832, h14066, hlam]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h13834, h14022, h14024, h8811, hc01, hc12, hlam, hphi, p14055_1]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h13831, hlam, p14055_1]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h14023, hlam, p14055_1]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [hlam, p14055_0]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h11548, h13831, h14022, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14055_1]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h14029, hlam, p14055_0]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h13832, hlam, p14055_1]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h14024, hlam, p14055_0]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h14027, hlam, p14055_0]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [hlam, p14055_0]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h14031, hlam, p14055_0]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h8811, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14055_1]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h14026, hlam, p14055_0]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h14022, h14024, h14026, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p14055_1]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [h14022, h14024, h14026, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14055_1]
                                      · have p14055_0 := h14055c.1
                                        have p14055_1 := h14055c.2.1
                                        have p14055_2 := h14055c.2.2.1
                                        have p14055_3 := h14055c.2.2.2
                                        linarith only [hlam, p14055_0]
                                · linarith only [h14028, h14050, hlam]
                              · linarith only [h14025, h14049, hlam]
                            · linarith only [h14048, hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            rcases p14033_3 (m.d 0 3) (by simp) with h14088 | h14088
                            · linarith only [h14088, h7360, hlam]
                            · rcases p14033_3 (m.d 1 3) (by simp) with h14090 | h14090
                              · rcases p14033_3 (m.d 2 3) (by simp) with h14091 | h14091
                                · linarith only [h14022, h14091, hlam]
                                · linarith only [h11548, h14091, hlam]
                              · linarith only [h14090, h7360, hlam]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h0, h11548, h14022, hc01, hc12, hlam, hphi, p14033_1]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            rcases p14033_3 (m.d 0 3) (by simp) with h14097 | h14097
                            · linarith only [h14097, h7360, hlam]
                            · linarith only [h13832, h14097, hlam]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            rcases p14033_3 (m.d 0 3) (by simp) with h14100 | h14100
                            · linarith only [h14100, h7360, hlam]
                            · linarith only [h13833, h14100, hlam]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h11548, h13831, h14022, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p14033_1]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h14022, hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            rcases p14033_3 (m.d 0 3) (by simp) with h14106 | h14106
                            · linarith only [h11548, h14106, hlam]
                            · linarith only [h13832, h14106, hlam]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            rcases p14033_3 (m.d 0 3) (by simp) with h14109 | h14109
                            · linarith only [h11548, h14109, hlam]
                            · linarith only [h13833, h14109, hlam]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h13832, hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h14024, hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h14027, hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h14031, hlam, p14033_1]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h13833, hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h14025, hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h14028, hlam, p14033_0]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [h11548, h13833, h14022, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14033_1]
                          · have p14033_0 := h14033c.1
                            have p14033_1 := h14033c.2.1
                            have p14033_2 := h14033c.2.2.1
                            have p14033_3 := h14033c.2.2.2
                            linarith only [hlam, p14033_0]
                    · linarith only [h11548, h13833, h14028, hlam]
                  · linarith only [h11548, h13832, h14027, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14124 | h14124
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14125 | h14125
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14126 | h14126
                      · linarith only [h11548, h13831, h14022, h14026, h14126, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14128 | h14128
                        · linarith only [h11548, h13831, h14022, h14026, h14124, h14128, h8811, hc01, hc12, hlam, hphi]
                        · rcases h3bigk with h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c | h14130c
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h7360, hlam, p14130_1]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h11548, hlam, p14130_1]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            rcases p14130_3 (m.d 0 3) (by simp) with h14134 | h14134
                            · rcases p14130_3 (m.d 1 3) (by simp) with h14135 | h14135
                              · rcases p14130_3 (m.d 2 3) (by simp) with h14136 | h14136
                                · rcases p14130_3 (m.d 3 4) (by simp) with h14137 | h14137
                                  · linarith only [h14137, hlam, p14130_0]
                                  · rcases p14130_3 (m.d 3 5) (by simp) with h14139 | h14139
                                    · linarith only [h13833, h14139, hlam]
                                    · linarith only [h14128, h14139, hlam]
                                · linarith only [h14124, h14136, hlam]
                              · linarith only [h14024, h14135, hlam]
                            · linarith only [h14134, hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            rcases p14130_3 (m.d 0 3) (by simp) with h14145 | h14145
                            · rcases p14130_3 (m.d 1 3) (by simp) with h14146 | h14146
                              · rcases p14130_3 (m.d 2 3) (by simp) with h14147 | h14147
                                · rcases p14130_3 (m.d 3 4) (by simp) with h14148 | h14148
                                  · linarith only [h13832, h14148, hlam]
                                  · rcases p14130_3 (m.d 3 5) (by simp) with h14150 | h14150
                                    · linarith only [h14150, hlam, p14130_0]
                                    · rcases h4bigk with h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c | h14152c
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [hlam, p14152_0]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h8811, hlam, p14152_0]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h14026, h8811, hc24, hc45, hlam, hphi, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h11548, h13831, h14022, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h13834, hlam, p14152_0]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h14026, hc04, hc45, hlam, hphi, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [hlam, p14152_0]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h14026, hc24, hc45, hlam, hphi, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h14026, hc34, hc45, hlam, hphi, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h14026, hlam, p14152_0]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h13831, hlam, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h14023, hlam, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [hlam, p14152_0]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h11548, h13831, h14022, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h14126, hlam, p14152_0]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h13832, hlam, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h14024, hlam, p14152_0]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h14124, hlam, p14152_0]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [hlam, p14152_0]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h14128, hlam, p14152_0]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [h8811, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [hc14, hc45, hlam, hphi, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [hc24, hc45, hlam, hphi, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [hc34, hc45, hlam, hphi, p14152_1]
                                      · have p14152_0 := h14152c.1
                                        have p14152_1 := h14152c.2.1
                                        have p14152_2 := h14152c.2.2.1
                                        have p14152_3 := h14152c.2.2.2
                                        linarith only [hlam, p14152_0]
                                · linarith only [h14125, h14147, hlam]
                              · linarith only [h14025, h14146, hlam]
                            · linarith only [h14145, hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            rcases p14130_3 (m.d 0 3) (by simp) with h14181 | h14181
                            · linarith only [h14181, h7360, hlam]
                            · rcases p14130_3 (m.d 1 3) (by simp) with h14183 | h14183
                              · rcases p14130_3 (m.d 2 3) (by simp) with h14184 | h14184
                                · linarith only [h14022, h14184, hlam]
                                · linarith only [h11548, h14184, hlam]
                              · linarith only [h14183, h7360, hlam]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h11548, h13831, h14022, h14124, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14130_1]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            rcases p14130_3 (m.d 0 3) (by simp) with h14190 | h14190
                            · linarith only [h14190, h7360, hlam]
                            · linarith only [h13832, h14190, hlam]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            rcases p14130_3 (m.d 0 3) (by simp) with h14193 | h14193
                            · linarith only [h14193, h7360, hlam]
                            · linarith only [h13833, h14193, hlam]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h11548, h13831, h14022, h14124, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14130_1]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h14022, hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            rcases p14130_3 (m.d 0 3) (by simp) with h14199 | h14199
                            · linarith only [h11548, h14199, hlam]
                            · linarith only [h13832, h14199, hlam]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            rcases p14130_3 (m.d 0 3) (by simp) with h14202 | h14202
                            · linarith only [h11548, h14202, hlam]
                            · linarith only [h13833, h14202, hlam]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h13832, hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h14024, hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h14124, hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h14128, hlam, p14130_1]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h13833, hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h14025, hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h14125, hlam, p14130_0]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [h11548, h13833, h14022, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14130_1]
                          · have p14130_0 := h14130c.1
                            have p14130_1 := h14130c.2.1
                            have p14130_2 := h14130c.2.2.1
                            have p14130_3 := h14130c.2.2.2
                            linarith only [hlam, p14130_0]
                    · linarith only [h11548, h13833, h14125, hlam]
                  · linarith only [h11548, h13832, h14124, hlam]
              · linarith only [h11548, h13833, h14022, h14025, hlam]
            · linarith only [h11548, h13831, h13832, h14022, h14024, hlam]
          · linarith only [h11548, h14022, h14023, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h14220 | h14220
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14221 | h14221
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14222 | h14222
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14223 | h14223
                · linarith only [h13834, h14022, h14220, h14223, h8811, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14225 | h14225
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14226 | h14226
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14227 | h14227
                      · linarith only [h14223, h14227, h8811, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14229 | h14229
                        · linarith only [h14223, h14229, h8811, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h3bigk with h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c | h14231c
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [hlam, p14231_0]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [h7360, hlam, p14231_1]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [h11548, hlam, p14231_1]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            rcases p14231_3 (m.d 0 3) (by simp) with h14235 | h14235
                            · rcases p14231_3 (m.d 1 3) (by simp) with h14236 | h14236
                              · rcases p14231_3 (m.d 2 3) (by simp) with h14237 | h14237
                                · rcases p14231_3 (m.d 3 4) (by simp) with h14238 | h14238
                                  · linarith only [h14238, hlam, p14231_0]
                                  · rcases p14231_3 (m.d 3 5) (by simp) with h14240 | h14240
                                    · linarith only [h13833, h14240, hlam]
                                    · linarith only [h14229, h14240, hlam]
                                · linarith only [h14225, h14237, hlam]
                              · linarith only [h14221, h14236, hlam]
                            · linarith only [h14235, hlam, p14231_0]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            rcases p14231_3 (m.d 0 3) (by simp) with h14246 | h14246
                            · rcases p14231_3 (m.d 1 3) (by simp) with h14247 | h14247
                              · rcases p14231_3 (m.d 2 3) (by simp) with h14248 | h14248
                                · rcases p14231_3 (m.d 3 4) (by simp) with h14249 | h14249
                                  · linarith only [h13832, h14249, hlam]
                                  · rcases p14231_3 (m.d 3 5) (by simp) with h14251 | h14251
                                    · linarith only [h14251, hlam, p14231_0]
                                    · rcases h4bigk with h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c | h14253c
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [hlam, p14253_0]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h8811, hlam, p14253_0]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h14223, h8811, hc24, hc45, hlam, hphi, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h14223, h8811, hc34, hc45, hlam, hphi, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h13834, hlam, p14253_0]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h14223, hc04, hc45, hlam, hphi, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [hlam, p14253_0]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h14223, hc24, hc45, hlam, hphi, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h14223, hc34, hc45, hlam, hphi, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h14223, hlam, p14253_0]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h13831, hlam, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h14220, hlam, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [hlam, p14253_0]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h0, h13831, h14022, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h14227, hlam, p14253_0]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h13832, hlam, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h14221, hlam, p14253_0]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h14225, hlam, p14253_0]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [hlam, p14253_0]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h14229, hlam, p14253_0]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [hc04, hc45, hlam, hphi, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [hc14, hc45, hlam, hphi, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [h14225, hc34, hc45, hlam, hphi, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [hc34, hc45, hlam, hphi, p14253_1]
                                      · have p14253_0 := h14253c.1
                                        have p14253_1 := h14253c.2.1
                                        have p14253_2 := h14253c.2.2.1
                                        have p14253_3 := h14253c.2.2.2
                                        linarith only [hlam, p14253_0]
                                · linarith only [h14226, h14248, hlam]
                              · linarith only [h14222, h14247, hlam]
                            · linarith only [h14246, hlam, p14231_0]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            rcases p14231_3 (m.d 0 3) (by simp) with h14282 | h14282
                            · linarith only [h14282, h7360, hlam]
                            · rcases p14231_3 (m.d 1 3) (by simp) with h14284 | h14284
                              · rcases p14231_3 (m.d 2 3) (by simp) with h14285 | h14285
                                · rcases p14231_3 (m.d 3 4) (by simp) with h14286 | h14286
                                  · linarith only [h14221, h14286, hlam]
                                  · rcases p14231_3 (m.d 3 5) (by simp) with h14288 | h14288
                                    · linarith only [h14222, h14288, hlam]
                                    · rcases h4bigk with h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c | h14290c
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [hlam, p14290_0]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h8811, hlam, p14290_0]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h11548, h13831, h14022, h14225, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14231_1, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h11548, h13831, h14022, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14231_1, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h13834, hlam, p14290_0]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h8811, hc01, hc14, hlam, hphi, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [hlam, p14290_0]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h14022, h14220, h14225, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h14022, h14220, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h14223, hlam, p14290_0]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h13831, hlam, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h14220, hlam, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [hlam, p14290_0]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h11548, h13831, h14022, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14231_1, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h14227, hlam, p14290_0]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h13832, hlam, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h14221, hlam, p14290_0]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h14225, hlam, p14290_0]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [hlam, p14290_0]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h14229, hlam, p14290_0]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h8811, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [hc14, hc45, hlam, hphi, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [h14225, hc34, hc45, hlam, hphi, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [hc34, hc45, hlam, hphi, p14290_1]
                                      · have p14290_0 := h14290c.1
                                        have p14290_1 := h14290c.2.1
                                        have p14290_2 := h14290c.2.2.1
                                        have p14290_3 := h14290c.2.2.2
                                        linarith only [hlam, p14290_0]
                                · linarith only [h11548, h14285, hlam]
                              · linarith only [h14284, h7360, hlam]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [hlam, p14231_0]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [h14022, hlam, p14231_1]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            rcases p14231_3 (m.d 0 3) (by simp) with h14320 | h14320
                            · linarith only [h14320, h7360, hlam]
                            · linarith only [h13832, h14320, hlam]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            rcases p14231_3 (m.d 0 3) (by simp) with h14323 | h14323
                            · linarith only [h14323, h7360, hlam]
                            · linarith only [h13833, h14323, hlam]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            rcases p14231_3 (m.d 0 3) (by simp) with h14326 | h14326
                            · linarith only [h11548, h14326, hlam]
                            · rcases p14231_3 (m.d 1 3) (by simp) with h14328 | h14328
                              · linarith only [h14022, h14328, hlam]
                              · linarith only [h14328, h7360, hlam]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [h7360, hc01, hc23, hlam, hphi, ht12, p14231_1]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [hlam, p14231_0]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            rcases p14231_3 (m.d 0 3) (by simp) with h14333 | h14333
                            · linarith only [h11548, h14333, hlam]
                            · linarith only [h13832, h14333, hlam]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            rcases p14231_3 (m.d 0 3) (by simp) with h14336 | h14336
                            · linarith only [h11548, h14336, hlam]
                            · linarith only [h13833, h14336, hlam]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [h13832, hlam, p14231_0]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [h14221, hlam, p14231_0]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [h14225, hlam, p14231_0]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [hlam, p14231_0]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [h14229, hlam, p14231_1]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [h13833, hlam, p14231_0]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [h14222, hlam, p14231_0]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [h14226, hlam, p14231_0]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            rcases p14231_3 (m.d 0 3) (by simp) with h14347 | h14347
                            · rcases p14231_3 (m.d 1 3) (by simp) with h14348 | h14348
                              · rcases p14231_3 (m.d 2 3) (by simp) with h14349 | h14349
                                · rcases p14231_3 (m.d 3 4) (by simp) with h14350 | h14350
                                  · linarith only [h14229, h14350, hlam]
                                  · rcases p14231_3 (m.d 3 5) (by simp) with h14352 | h14352
                                    · rcases h4bigk with h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c | h14353c
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [hlam, p14353_0]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h8811, hlam, p14353_0]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h11548, h13831, h14225, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h11548, h13831, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h13834, hlam, p14353_0]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h14220, h8811, hc01, hc12, hlam, hphi, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [hlam, p14353_0]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h14022, h14220, h14225, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h14022, h14220, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h14223, hlam, p14353_0]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h13831, hlam, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h14220, hlam, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [hlam, p14353_0]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h0, h13831, h14022, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h14227, hlam, p14353_0]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h13832, hlam, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h14221, hlam, p14353_0]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h14225, hlam, p14353_0]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [hlam, p14353_0]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h14229, hlam, p14353_0]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [h8811, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [hc14, hc45, hlam, hphi, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [hc24, hc45, hlam, hphi, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [hc34, hc45, hlam, hphi, p14353_1]
                                      · have p14353_0 := h14353c.1
                                        have p14353_1 := h14353c.2.1
                                        have p14353_2 := h14353c.2.2.1
                                        have p14353_3 := h14353c.2.2.2
                                        linarith only [hlam, p14353_0]
                                    · linarith only [h14229, h14352, hlam]
                                · linarith only [h14225, h14349, hlam]
                              · linarith only [h14221, h14348, hlam]
                            · linarith only [h13832, h14347, hlam]
                          · have p14231_0 := h14231c.1
                            have p14231_1 := h14231c.2.1
                            have p14231_2 := h14231c.2.2.1
                            have p14231_3 := h14231c.2.2.2
                            linarith only [hlam, p14231_0]
                    · linarith only [h13833, h14022, h14226, h7360, hlam]
                  · linarith only [h0, h14022, h14225, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h13833, h14222, h7360, hlam]
            · linarith only [h13832, h14022, h14220, h14221, h7360, h8811, hc01, hc23, hlam, hphi, ht12]
          · linarith only [h0, h11548, h13831, h14220, h7360, hc01, hc13, hlam, hphi]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h14389 | h14389
      · linarith only [h11548, h13831, h13833, h14389, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h14391 | h14391
        · rcases m.htr 1 2 4 (by decide) (by decide) with h14392 | h14392
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14393 | h14393
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14394 | h14394
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14395 | h14395
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14396 | h14396
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14397 | h14397
                    · linarith only [h11548, h13831, h13833, h14391, h14397, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h11548, h13831, h14391, h14394, h14396, h14397, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h11548, h13832, h14396, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14401 | h14401
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14402 | h14402
                    · linarith only [h13833, h14391, h14402, h7360, hc01, hc12, hlam, hphi]
                    · linarith only [h11548, h13831, h14391, h14394, h14401, h14402, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h11548, h13832, h14401, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14406 | h14406
                · linarith only [h14389, h14393, h14394, h14406, h8811, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14408 | h14408
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14409 | h14409
                    · linarith only [h14391, h14394, h14409, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14411 | h14411
                      · linarith only [h13831, h14406, h14411, h8811, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14413 | h14413
                        · linarith only [h11548, h13831, h14391, h14394, h14406, h14408, h14413, h8811, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h11548, h13831, h14391, h14394, h14408, h14413, hc34, hc45, hlam, hphi]
                  · linarith only [h11548, h13832, h14408, hlam]
            · linarith only [h11548, h13831, h13832, h14393, h7360, hc01, hc23, hlam, hphi, ht12]
          · linarith only [h11548, h13831, h14392, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h14419 | h14419
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14420 | h14420
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14421 | h14421
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14422 | h14422
                · linarith only [h14389, h14391, h14419, h14422, h8811, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14424 | h14424
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14425 | h14425
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14426 | h14426
                      · linarith only [h11548, h13831, h13833, h14391, h14421, h14422, h14426, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14428 | h14428
                        · linarith only [h11548, h13831, h13833, h14391, h14421, h14422, h14424, h14428, h8811, hc01, hc23, hlam, hphi, ht12]
                        · rcases h3bigk with h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c | h14430c
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [hlam, p14430_0]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h7360, hlam, p14430_1]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h11548, hlam, p14430_1]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h13833, h14391, h14421, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14430_1]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h13833, hlam, p14430_0]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            rcases p14430_3 (m.d 0 3) (by simp) with h14436 | h14436
                            · linarith only [h14436, h7360, hlam]
                            · rcases p14430_3 (m.d 1 3) (by simp) with h14438 | h14438
                              · rcases p14430_3 (m.d 2 3) (by simp) with h14439 | h14439
                                · rcases p14430_3 (m.d 3 4) (by simp) with h14440 | h14440
                                  · linarith only [h14420, h14440, hlam]
                                  · rcases p14430_3 (m.d 3 5) (by simp) with h14442 | h14442
                                    · linarith only [h14421, h14442, hlam]
                                    · linarith only [h13833, h14442, hlam]
                                · linarith only [h11548, h14439, hlam]
                              · linarith only [h14438, h7360, hlam]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [hlam, p14430_0]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h14391, hlam, p14430_1]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h13832, h13833, h14421, hlam, p14430_2]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h11548, h13833, h14391, hc02, hc23, hlam, hphi, p14430_1]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            rcases p14430_3 (m.d 0 3) (by simp) with h14451 | h14451
                            · linarith only [h11548, h14451, hlam]
                            · rcases p14430_3 (m.d 1 3) (by simp) with h14453 | h14453
                              · linarith only [h14391, h14453, hlam]
                              · linarith only [h14453, h7360, hlam]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h7360, hc01, hc23, hlam, hphi, ht12, p14430_1]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [hlam, p14430_0]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h11548, h13831, h13833, h14391, h14421, h14424, hlam, p14430_2]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h11548, h13831, h13833, h14424, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14430_1]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h13832, hlam, p14430_0]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h14420, hlam, p14430_0]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h14424, hlam, p14430_0]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [hlam, p14430_0]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h14428, hlam, p14430_1]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h11548, h13831, h14421, h14424, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14430_1]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h14421, hlam, p14430_0]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [h14425, hlam, p14430_0]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            rcases p14430_3 (m.d 0 3) (by simp) with h14468 | h14468
                            · linarith only [h13833, h14468, hlam]
                            · linarith only [h13832, h14468, hlam]
                          · have p14430_0 := h14430c.1
                            have p14430_1 := h14430c.2.1
                            have p14430_2 := h14430c.2.2.1
                            have p14430_3 := h14430c.2.2.2
                            linarith only [hlam, p14430_0]
                    · linarith only [h14391, h14421, h14425, hlam]
                  · linarith only [h13832, h14391, h14424, h7360, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14474 | h14474
                · linarith only [h14389, h14391, h14419, h14421, h14474, h8811, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14476 | h14476
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14477 | h14477
                    · linarith only [h0, h14391, h14421, h14477, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h14391, h14419, h14477, h8811, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h14391, h14419, h14476, h8811, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h11548, h13831, h13832, h14420, h7360, hlam]
          · linarith only [h0, h11548, h13831, h14419, h7360, hc01, hc13, hlam, hphi]
  · linarith only [h11548, h13831, h13832, hlam]

end R2N4
