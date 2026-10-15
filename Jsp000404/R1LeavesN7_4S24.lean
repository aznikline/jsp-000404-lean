import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8080000 in
set_option maxHeartbeats 8080000 in
theorem r1l7_11_23_L_I_H_I_s14_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h14856 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h17362 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h17828 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  rcases m.htr 0 3 5 (by decide) (by decide) with h17829 | h17829
  · rcases m.htr 0 4 5 (by decide) (by decide) with h17830 | h17830
    · rcases m.htr 1 2 3 (by decide) (by decide) with h17831 | h17831
      · rcases m.htr 1 2 4 (by decide) (by decide) with h17832 | h17832
        · rcases m.htr 1 2 5 (by decide) (by decide) with h17833 | h17833
          · rcases m.htr 1 3 4 (by decide) (by decide) with h17834 | h17834
            · rcases m.htr 1 3 5 (by decide) (by decide) with h17835 | h17835
              · rcases m.htr 1 4 5 (by decide) (by decide) with h17836 | h17836
                · rcases m.htr 2 3 4 (by decide) (by decide) with h17837 | h17837
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h17838 | h17838
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h17839 | h17839
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h17840 | h17840
                        · rcases h1bigk with h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c | h17841c
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [hlam, p17841_0]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h0, hlam, p17841_0]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h11385, hlam, p17841_0]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h12794, hlam, p17841_0]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h13812, hlam, p17841_0]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            rcases p17841_3 (m.d 0 1) (by simp) with h17847 | h17847
                            · linarith only [h17847, hlam, p17841_0]
                            · rcases p17841_3 (m.d 1 2) (by simp) with h17849 | h17849
                              · rcases p17841_3 (m.d 1 3) (by simp) with h17850 | h17850
                                · linarith only [h17831, h17850, hlam]
                                · linarith only [h11385, h17850, hlam]
                              · linarith only [h17849, hlam, p17841_0]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [hlam, p17841_0]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h14856, h17828, h17831, h17840, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p17841_1]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h12794, hc01, hc12, hlam, hphi, p17841_1]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h13812, hc01, hc12, hlam, hphi, p17841_1]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            rcases p17841_3 (m.d 0 1) (by simp) with h17858 | h17858
                            · linarith only [h17858, hlam, p17841_0]
                            · rcases p17841_3 (m.d 1 2) (by simp) with h17860 | h17860
                              · rcases p17841_3 (m.d 1 3) (by simp) with h17861 | h17861
                                · rcases p17841_3 (m.d 1 4) (by simp) with h17862 | h17862
                                  · linarith only [h17834, h17862, hlam]
                                  · linarith only [h12794, h17862, hlam]
                                · linarith only [h17861, hlam, p17841_0]
                              · linarith only [h0, h17860, hlam]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h17831, hlam, p17841_1]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [hlam, p17841_0]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h0, h17362, h17832, hc01, hc13, hlam, hphi, p17841_1]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h13812, h17831, hc01, hc12, hlam, hphi, p17841_1]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            rcases p17841_3 (m.d 0 1) (by simp) with h17871 | h17871
                            · linarith only [h17871, hlam, p17841_0]
                            · rcases p17841_3 (m.d 1 2) (by simp) with h17873 | h17873
                              · rcases p17841_3 (m.d 1 3) (by simp) with h17874 | h17874
                                · rcases p17841_3 (m.d 1 4) (by simp) with h17875 | h17875
                                  · rcases p17841_3 (m.d 1 5) (by simp) with h17876 | h17876
                                    · linarith only [h17836, h17876, hlam]
                                    · linarith only [h13812, h17876, hlam]
                                  · linarith only [h17875, hlam, p17841_0]
                                · linarith only [h11385, h17874, hlam]
                              · linarith only [h0, h17873, hlam]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h17832, hlam, p17841_1]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h17834, hlam, p17841_0]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [hlam, p17841_0]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h13812, hc01, hc14, hlam, hphi, p17841_1]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            rcases p17841_3 (m.d 0 1) (by simp) with h17886 | h17886
                            · linarith only [h17886, hlam, p17841_0]
                            · rcases p17841_3 (m.d 1 2) (by simp) with h17888 | h17888
                              · rcases p17841_3 (m.d 1 3) (by simp) with h17889 | h17889
                                · rcases p17841_3 (m.d 1 4) (by simp) with h17890 | h17890
                                  · rcases p17841_3 (m.d 1 5) (by simp) with h17891 | h17891
                                    · rcases h3bigk with h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c | h17892c
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [hlam, p17892_0]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h11385, hlam, p17892_1]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h14856, hlam, p17892_1]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17840, hc03, hc45, hlam, hphi, ht0b, ht5b, p17892_1]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h14856, h17831, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p17892_1]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h11385, h17831, hc01, hc12, hlam, hphi, p17892_1]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [hlam, p17892_0]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h0, h14856, h17831, hc01, hc12, hlam, hphi, p17892_1]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17831, h17840, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p17892_1]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        rcases p17892_3 (m.d 0 3) (by simp) with h17902 | h17902
                                        · linarith only [h11385, h17902, hlam]
                                        · linarith only [h17829, h17902, hlam]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17828, h17840, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p17892_1]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17831, hlam, p17892_0]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [hlam, p17892_0]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17831, h17840, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p17892_1]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17831, h17840, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p17892_1]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17828, hlam, p17892_0]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17834, hlam, p17892_0]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17837, hlam, p17892_0]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [hlam, p17892_0]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17828, h17840, hc03, hc45, hlam, hphi, ht0b, ht5b, p17892_1]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17829, hlam, p17892_0]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17835, hlam, p17892_0]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17838, hlam, p17892_0]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [h17840, hlam, p17892_0]
                                      · have p17892_0 := h17892c.1
                                        have p17892_1 := h17892c.2.1
                                        have p17892_2 := h17892c.2.2.1
                                        have p17892_3 := h17892c.2.2.2
                                        linarith only [hlam, p17892_0]
                                    · linarith only [h17891, hlam, p17841_0]
                                  · linarith only [h12794, h17890, hlam]
                                · linarith only [h11385, h17889, hlam]
                              · linarith only [h0, h17888, hlam]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h17833, hlam, p17841_1]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h17835, hlam, p17841_0]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [h17836, hlam, p17841_0]
                          · have p17841_0 := h17841c.1
                            have p17841_1 := h17841c.2.1
                            have p17841_2 := h17841c.2.2.1
                            have p17841_3 := h17841c.2.2.2
                            linarith only [hlam, p17841_0]
                        · rcases h1bigk with h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c | h17928c
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [hlam, p17928_0]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h0, hlam, p17928_0]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h11385, hlam, p17928_0]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h12794, hlam, p17928_0]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h13812, hlam, p17928_0]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            rcases p17928_3 (m.d 0 1) (by simp) with h17934 | h17934
                            · linarith only [h17934, hlam, p17928_0]
                            · rcases p17928_3 (m.d 1 2) (by simp) with h17936 | h17936
                              · rcases p17928_3 (m.d 1 3) (by simp) with h17937 | h17937
                                · linarith only [h17831, h17937, hlam]
                                · linarith only [h11385, h17937, hlam]
                              · linarith only [h17936, hlam, p17928_0]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [hlam, p17928_0]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h11385, hc01, hc12, hlam, hphi, p17928_1]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h12794, h17830, h17840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17928_1]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h13812, hc01, hc12, hlam, hphi, p17928_1]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            rcases p17928_3 (m.d 0 1) (by simp) with h17945 | h17945
                            · linarith only [h17945, hlam, p17928_0]
                            · rcases p17928_3 (m.d 1 2) (by simp) with h17947 | h17947
                              · rcases p17928_3 (m.d 1 3) (by simp) with h17948 | h17948
                                · rcases p17928_3 (m.d 1 4) (by simp) with h17949 | h17949
                                  · linarith only [h17834, h17949, hlam]
                                  · linarith only [h12794, h17949, hlam]
                                · linarith only [h17948, hlam, p17928_0]
                              · linarith only [h0, h17947, hlam]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h17831, hlam, p17928_1]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [hlam, p17928_0]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h17362, h17830, h17832, h17840, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17928_1]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h13812, h17831, hc01, hc12, hlam, hphi, p17928_1]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            rcases p17928_3 (m.d 0 1) (by simp) with h17958 | h17958
                            · linarith only [h17958, hlam, p17928_0]
                            · rcases p17928_3 (m.d 1 2) (by simp) with h17960 | h17960
                              · rcases p17928_3 (m.d 1 3) (by simp) with h17961 | h17961
                                · rcases p17928_3 (m.d 1 4) (by simp) with h17962 | h17962
                                  · rcases p17928_3 (m.d 1 5) (by simp) with h17963 | h17963
                                    · linarith only [h17836, h17963, hlam]
                                    · linarith only [h13812, h17963, hlam]
                                  · linarith only [h17962, hlam, p17928_0]
                                · linarith only [h11385, h17961, hlam]
                              · linarith only [h0, h17960, hlam]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h17832, hlam, p17928_1]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h17834, hlam, p17928_0]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [hlam, p17928_0]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h13812, hc01, hc14, hlam, hphi, p17928_1]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            rcases p17928_3 (m.d 0 1) (by simp) with h17973 | h17973
                            · linarith only [h17973, hlam, p17928_0]
                            · rcases p17928_3 (m.d 1 2) (by simp) with h17975 | h17975
                              · rcases p17928_3 (m.d 1 3) (by simp) with h17976 | h17976
                                · rcases p17928_3 (m.d 1 4) (by simp) with h17977 | h17977
                                  · rcases p17928_3 (m.d 1 5) (by simp) with h17978 | h17978
                                    · rcases h3bigk with h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c | h17979c
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [hlam, p17979_0]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h11385, hlam, p17979_1]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h14856, hlam, p17979_1]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h14856, h17831, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17979_1]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h14856, h17831, h17840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17979_1]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h11385, h17831, hc01, hc12, hlam, hphi, p17979_1]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [hlam, p17979_0]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h14856, h17828, h17830, h17831, h17840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17979_1]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        rcases p17979_3 (m.d 0 3) (by simp) with h17988 | h17988
                                        · linarith only [h11385, h17988, hlam]
                                        · linarith only [h17828, h17988, hlam]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        rcases p17979_3 (m.d 0 3) (by simp) with h17991 | h17991
                                        · linarith only [h11385, h17991, hlam]
                                        · linarith only [h17829, h17991, hlam]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h17828, h17830, h17840, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17979_1]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h17831, hlam, p17979_0]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [hlam, p17979_0]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h17831, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17979_1]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h17831, h17840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17979_1]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h17828, hlam, p17979_0]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h17834, hlam, p17979_0]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h17837, hlam, p17979_0]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [hlam, p17979_0]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h17840, hlam, p17979_1]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h17829, hlam, p17979_0]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h17835, hlam, p17979_0]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h17838, hlam, p17979_0]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [h17829, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p17979_1]
                                      · have p17979_0 := h17979c.1
                                        have p17979_1 := h17979c.2.1
                                        have p17979_2 := h17979c.2.2.1
                                        have p17979_3 := h17979c.2.2.2
                                        linarith only [hlam, p17979_0]
                                    · linarith only [h17978, hlam, p17928_0]
                                  · linarith only [h12794, h17977, hlam]
                                · linarith only [h11385, h17976, hlam]
                              · linarith only [h0, h17975, hlam]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h17833, hlam, p17928_1]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h17835, hlam, p17928_0]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [h17836, hlam, p17928_0]
                          · have p17928_0 := h17928c.1
                            have p17928_1 := h17928c.2.1
                            have p17928_2 := h17928c.2.2.1
                            have p17928_3 := h17928c.2.2.2
                            linarith only [hlam, p17928_0]
                      · linarith only [h17362, h17830, h17839, hlam]
                    · linarith only [h14856, h17829, h17838, hlam]
                  · linarith only [h14856, h17828, h17837, hlam]
                · linarith only [h12794, h17362, h17830, h17836, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h11385, h14856, h17829, h17835, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h14856, h17828, h17831, h17834, hlam]
          · linarith only [h0, h14856, h17831, h17833, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h14856, h17831, h17832, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h18025 | h18025
        · linarith only [h0, h17362, h17831, h18025, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h18027 | h18027
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18028 | h18028
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18029 | h18029
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18030 | h18030
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18031 | h18031
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18032 | h18032
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18033 | h18033
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18034 | h18034
                        · rcases h1bigk with h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c | h18035c
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h0, hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h11385, hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h12794, hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h13812, hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h18025, h18031, hc01, hc23, hlam, hphi, ht12, p18035_1]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h17831, hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h18025, hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h13812, h18025, h18031, hc01, hc23, hlam, hphi, ht12, p18035_1]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            rcases p18035_3 (m.d 0 1) (by simp) with h18046 | h18046
                            · linarith only [h18046, hlam, p18035_0]
                            · rcases p18035_3 (m.d 1 2) (by simp) with h18048 | h18048
                              · linarith only [h17831, h18048, hlam]
                              · linarith only [h0, h18048, hlam]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h0, h17831, hc01, hc23, hlam, hphi, ht12, p18035_1]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h12794, h17831, hc01, hc23, hlam, hphi, ht12, p18035_1]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h13812, h17831, hc01, hc23, hlam, hphi, ht12, p18035_1]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            rcases p18035_3 (m.d 0 1) (by simp) with h18055 | h18055
                            · linarith only [h18055, hlam, p18035_0]
                            · rcases p18035_3 (m.d 1 2) (by simp) with h18057 | h18057
                              · linarith only [h18025, h18057, hlam]
                              · linarith only [h0, h18057, hlam]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h13812, h18027, hc01, hc14, hlam, hphi, p18035_1]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h18028, hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h13812, h18025, h18031, hc01, hc23, hlam, hphi, ht12, p18035_1]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h17831, h18027, hc01, hc23, hlam, hphi, ht12, p18035_1]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h18027, hlam, p18035_1]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h18029, hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [h18030, hlam, p18035_0]
                          · have p18035_0 := h18035c.1
                            have p18035_1 := h18035c.2.1
                            have p18035_2 := h18035c.2.2.1
                            have p18035_3 := h18035c.2.2.2
                            linarith only [hlam, p18035_0]
                        · rcases h1bigk with h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c | h18069c
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h0, hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h11385, hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h12794, hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h13812, hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h18025, h18031, hc01, hc23, hlam, hphi, ht12, p18069_1]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h17831, hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h18025, hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h13812, h18025, h18031, hc01, hc23, hlam, hphi, ht12, p18069_1]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            rcases p18069_3 (m.d 0 1) (by simp) with h18080 | h18080
                            · linarith only [h18080, hlam, p18069_0]
                            · rcases p18069_3 (m.d 1 2) (by simp) with h18082 | h18082
                              · linarith only [h17831, h18082, hlam]
                              · linarith only [h0, h18082, hlam]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h0, h17831, hc01, hc23, hlam, hphi, ht12, p18069_1]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h12794, h17831, hc01, hc23, hlam, hphi, ht12, p18069_1]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h13812, h17831, hc01, hc23, hlam, hphi, ht12, p18069_1]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            rcases p18069_3 (m.d 0 1) (by simp) with h18089 | h18089
                            · linarith only [h18089, hlam, p18069_0]
                            · rcases p18069_3 (m.d 1 2) (by simp) with h18091 | h18091
                              · linarith only [h18025, h18091, hlam]
                              · linarith only [h0, h18091, hlam]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h18027, h18033, h18034, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18069_1]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h18028, hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h13812, h18025, h18031, hc01, hc23, hlam, hphi, ht12, p18069_1]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h17831, h18027, hc01, hc23, hlam, hphi, ht12, p18069_1]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h18027, hlam, p18069_1]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h18029, hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [h18030, hlam, p18069_0]
                          · have p18069_0 := h18069c.1
                            have p18069_1 := h18069c.2.1
                            have p18069_2 := h18069c.2.2.1
                            have p18069_3 := h18069c.2.2.2
                            linarith only [hlam, p18069_0]
                      · linarith only [h0, h17830, h18025, h18033, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h11385, h17829, h17831, h18032, hlam]
                  · linarith only [h11385, h17828, h17831, h18031, hlam]
                · linarith only [h12794, h13812, h17830, h18025, h18027, h18030, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h11385, h17829, h18029, hlam]
            · linarith only [h11385, h17828, h18028, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18109 | h18109
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18110 | h18110
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18111 | h18111
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18112 | h18112
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18113 | h18113
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18114 | h18114
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18115 | h18115
                        · rcases h1bigk with h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c | h18116c
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h0, hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h11385, hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h12794, hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h13812, hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h18027, hc01, hc25, hlam, hphi, ht12, p18116_1]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h17831, hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h18025, hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h18027, hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            rcases p18116_3 (m.d 0 1) (by simp) with h18127 | h18127
                            · linarith only [h18127, hlam, p18116_0]
                            · rcases p18116_3 (m.d 1 2) (by simp) with h18129 | h18129
                              · linarith only [h17831, h18129, hlam]
                              · linarith only [h0, h18129, hlam]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h0, hc01, hc13, hlam, hphi, p18116_1]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h0, h17831, h18027, h18111, hc01, hc23, hlam, hphi, ht12, p18116_1]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h0, h17831, h18027, hc01, hc23, hlam, hphi, ht12, p18116_1]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            rcases p18116_3 (m.d 0 1) (by simp) with h18136 | h18136
                            · linarith only [h18136, hlam, p18116_0]
                            · rcases p18116_3 (m.d 1 2) (by simp) with h18138 | h18138
                              · linarith only [h18025, h18138, hlam]
                              · linarith only [h0, h18138, hlam]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p18116_1]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h18109, hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h0, h18025, h18027, h18112, hc01, hc23, hlam, hphi, ht12, p18116_1]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            rcases p18116_3 (m.d 0 1) (by simp) with h18145 | h18145
                            · linarith only [h18145, hlam, p18116_0]
                            · rcases p18116_3 (m.d 1 2) (by simp) with h18147 | h18147
                              · linarith only [h18027, h18147, hlam]
                              · linarith only [h0, h18147, hlam]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p18116_1]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h18110, hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [h18111, hlam, p18116_0]
                          · have p18116_0 := h18116c.1
                            have p18116_1 := h18116c.2.1
                            have p18116_2 := h18116c.2.2.1
                            have p18116_3 := h18116c.2.2.2
                            linarith only [hlam, p18116_0]
                        · rcases h1bigk with h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c | h18154c
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h0, hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h11385, hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h12794, hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h13812, hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h17831, hc01, hc23, hlam, hphi, ht12, p18154_1]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h17831, hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h18025, hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h18027, hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            rcases p18154_3 (m.d 0 1) (by simp) with h18165 | h18165
                            · linarith only [h18165, hlam, p18154_0]
                            · rcases p18154_3 (m.d 1 2) (by simp) with h18167 | h18167
                              · linarith only [h17831, h18167, hlam]
                              · linarith only [h0, h18167, hlam]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h0, h17831, hc01, hc23, hlam, hphi, ht12, p18154_1]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h12794, h17831, hc01, hc23, hlam, hphi, ht12, p18154_1]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h13812, h17831, hc01, hc23, hlam, hphi, ht12, p18154_1]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            rcases p18154_3 (m.d 0 1) (by simp) with h18174 | h18174
                            · linarith only [h18174, hlam, p18154_0]
                            · rcases p18154_3 (m.d 1 2) (by simp) with h18176 | h18176
                              · linarith only [h18025, h18176, hlam]
                              · linarith only [h0, h18176, hlam]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p18154_1]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h18109, hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h0, h18025, h18027, h18112, hc01, hc23, hlam, hphi, ht12, p18154_1]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            rcases p18154_3 (m.d 0 1) (by simp) with h18183 | h18183
                            · linarith only [h18183, hlam, p18154_0]
                            · rcases p18154_3 (m.d 1 2) (by simp) with h18185 | h18185
                              · linarith only [h18027, h18185, hlam]
                              · linarith only [h0, h18185, hlam]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p18154_1]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h18110, hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [h18111, hlam, p18154_0]
                          · have p18154_0 := h18154c.1
                            have p18154_1 := h18154c.2.1
                            have p18154_2 := h18154c.2.2.1
                            have p18154_3 := h18154c.2.2.2
                            linarith only [hlam, p18154_0]
                      · linarith only [h11385, h12794, h17828, h17830, h17831, h18025, h18114, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h11385, h17829, h17831, h18113, hlam]
                  · linarith only [h0, h17831, h18112, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h12794, h17830, h18111, hlam]
              · linarith only [h11385, h17829, h18110, hlam]
            · linarith only [h11385, h17828, h18109, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h18198 | h18198
      · rcases m.htr 1 2 4 (by decide) (by decide) with h18199 | h18199
        · rcases m.htr 1 2 5 (by decide) (by decide) with h18200 | h18200
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18201 | h18201
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18202 | h18202
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18203 | h18203
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18204 | h18204
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18205 | h18205
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18206 | h18206
                      · linarith only [h0, h17362, h17830, h18198, h18204, h18206, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h17362, h18201, h18203, h18206, hc01, hc13, hlam, hphi]
                    · linarith only [h14856, h17829, h18205, hlam]
                  · linarith only [h14856, h17828, h18204, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18211 | h18211
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18212 | h18212
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18213 | h18213
                      · linarith only [h12794, h18203, h18213, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18215 | h18215
                        · linarith only [h0, h17362, h17828, h18199, h18203, h18215, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases h1bigk with h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c | h18217c
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [hlam, p18217_0]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h0, hlam, p18217_0]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h11385, hlam, p18217_0]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h12794, hlam, p18217_0]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h13812, hlam, p18217_0]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            rcases p18217_3 (m.d 0 1) (by simp) with h18223 | h18223
                            · linarith only [h18223, hlam, p18217_0]
                            · rcases p18217_3 (m.d 1 2) (by simp) with h18225 | h18225
                              · rcases p18217_3 (m.d 1 3) (by simp) with h18226 | h18226
                                · linarith only [h18198, h18226, hlam]
                                · linarith only [h11385, h18226, hlam]
                              · linarith only [h18225, hlam, p18217_0]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [hlam, p18217_0]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h11385, hc01, hc12, hlam, hphi, p18217_1]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h0, h17362, h18199, hc01, hc12, hlam, hphi, p18217_1]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h13812, hc01, hc12, hlam, hphi, p18217_1]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            rcases p18217_3 (m.d 0 1) (by simp) with h18234 | h18234
                            · linarith only [h18234, hlam, p18217_0]
                            · rcases p18217_3 (m.d 1 2) (by simp) with h18236 | h18236
                              · rcases p18217_3 (m.d 1 3) (by simp) with h18237 | h18237
                                · rcases p18217_3 (m.d 1 4) (by simp) with h18238 | h18238
                                  · linarith only [h18201, h18238, hlam]
                                  · linarith only [h12794, h18238, hlam]
                                · linarith only [h18237, hlam, p18217_0]
                              · linarith only [h0, h18236, hlam]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h18198, hlam, p18217_1]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [hlam, p18217_0]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h0, h17362, h18199, hc01, hc13, hlam, hphi, p18217_1]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h0, h17362, h18198, h18199, h18203, hc01, hc12, hlam, hphi, p18217_1]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h18203, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p18217_1]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h18199, hlam, p18217_1]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h18201, hlam, p18217_0]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [hlam, p18217_0]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h18203, hlam, p18217_1]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            rcases p18217_3 (m.d 0 1) (by simp) with h18252 | h18252
                            · linarith only [h18252, hlam, p18217_0]
                            · rcases p18217_3 (m.d 1 2) (by simp) with h18254 | h18254
                              · rcases p18217_3 (m.d 1 3) (by simp) with h18255 | h18255
                                · rcases p18217_3 (m.d 1 4) (by simp) with h18256 | h18256
                                  · linarith only [h18203, h18256, hlam]
                                  · linarith only [h12794, h18256, hlam]
                                · linarith only [h11385, h18255, hlam]
                              · linarith only [h0, h18254, hlam]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h18200, hlam, p18217_1]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h18202, hlam, p18217_0]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [h12794, hc01, hc15, hlam, hphi, p18217_1]
                          · have p18217_0 := h18217c.1
                            have p18217_1 := h18217c.2.1
                            have p18217_2 := h18217c.2.2.1
                            have p18217_3 := h18217c.2.2.2
                            linarith only [hlam, p18217_0]
                    · linarith only [h14856, h17829, h18212, hlam]
                  · linarith only [h14856, h17828, h18211, hlam]
              · linarith only [h11385, h14856, h17829, h18198, h18202, hc01, hc12, hlam, hphi]
            · linarith only [h14856, h17828, h18198, h18201, hlam]
          · linarith only [h0, h14856, h18198, h18200, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h14856, h18198, h18199, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h18271 | h18271
        · linarith only [h0, h17362, h18198, h18271, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h18273 | h18273
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18274 | h18274
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18275 | h18275
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18276 | h18276
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18277 | h18277
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18278 | h18278
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18279 | h18279
                      · linarith only [h0, h17362, h17830, h18271, h18273, h18277, h18279, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h18271, h18273, h18276, h18279, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h17362, h17830, h18271, h18273, h18276, h18277, h18278, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h11385, h17828, h17830, h18198, h18273, h18276, h18277, hc01, hc12, hlam, hphi]
                · linarith only [h18271, h18273, h18276, hlam]
              · linarith only [h11385, h13812, h17829, h18198, h18273, h18275, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h11385, h17828, h18274, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18287 | h18287
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18288 | h18288
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18289 | h18289
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18290 | h18290
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18291 | h18291
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18292 | h18292
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18293 | h18293
                        · linarith only [h17828, h17830, h18293, hlam]
                        · rcases h1bigk with h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c | h18295c
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h0, hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h11385, hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h12794, hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h13812, hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h18273, hc01, hc25, hlam, hphi, ht12, p18295_1]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h18198, hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h18271, hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h18273, hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            rcases p18295_3 (m.d 0 1) (by simp) with h18306 | h18306
                            · linarith only [h18306, hlam, p18295_0]
                            · rcases p18295_3 (m.d 1 2) (by simp) with h18308 | h18308
                              · linarith only [h18198, h18308, hlam]
                              · linarith only [h0, h18308, hlam]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h0, h18198, hc01, hc23, hlam, hphi, ht12, p18295_1]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h12794, h18198, hc01, hc23, hlam, hphi, ht12, p18295_1]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h13812, h18198, hc01, hc23, hlam, hphi, ht12, p18295_1]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            rcases p18295_3 (m.d 0 1) (by simp) with h18315 | h18315
                            · linarith only [h18315, hlam, p18295_0]
                            · rcases p18295_3 (m.d 1 2) (by simp) with h18317 | h18317
                              · linarith only [h18271, h18317, hlam]
                              · linarith only [h0, h18317, hlam]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p18295_1]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h18287, hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h0, h17362, h17830, h18271, h18289, h18290, hc01, hc23, hlam, hphi, ht12, p18295_1]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            rcases p18295_3 (m.d 0 1) (by simp) with h18324 | h18324
                            · linarith only [h18324, hlam, p18295_0]
                            · rcases p18295_3 (m.d 1 2) (by simp) with h18326 | h18326
                              · linarith only [h18273, h18326, hlam]
                              · linarith only [h0, h18326, hlam]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p18295_1]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h18288, hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [h18289, hlam, p18295_0]
                          · have p18295_0 := h18295c.1
                            have p18295_1 := h18295c.2.1
                            have p18295_2 := h18295c.2.2.1
                            have p18295_3 := h18295c.2.2.2
                            linarith only [hlam, p18295_0]
                      · linarith only [h0, h18271, h18292, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h11385, h17829, h18198, h18291, hlam]
                  · linarith only [h17828, h17830, h18198, h18287, h18289, h18290, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18336 | h18336
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18337 | h18337
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18338 | h18338
                      · linarith only [h12794, h18289, h18336, h18338, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h18271, h18338, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h11385, h14856, h17829, h18337, hc01, hc13, hlam, hphi]
                  · linarith only [h11385, h17828, h18198, h18336, hlam]
              · linarith only [h11385, h17829, h18288, hlam]
            · linarith only [h11385, h17828, h18287, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h18345 | h18345
    · linarith only [h17828, h17829, h18345, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h18347 | h18347
      · rcases m.htr 1 2 4 (by decide) (by decide) with h18348 | h18348
        · rcases m.htr 1 2 5 (by decide) (by decide) with h18349 | h18349
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18350 | h18350
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18351 | h18351
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18352 | h18352
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18353 | h18353
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18354 | h18354
                    · linarith only [h17828, h17829, h18347, h18354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h14856, h18347, h18351, h18354, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11385, h14856, h17828, h18347, h18353, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18358 | h18358
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18359 | h18359
                    · linarith only [h17828, h17829, h18347, h18359, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h14856, h18351, h18359, hc01, hc13, hlam, hphi]
                  · linarith only [h0, h11385, h14856, h17828, h18347, h18358, hc01, hc12, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18363 | h18363
                · linarith only [h0, h17362, h18345, h18350, h18351, h18363, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18365 | h18365
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18366 | h18366
                    · linarith only [h11385, h18351, h18366, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18368 | h18368
                      · linarith only [h13812, h18348, h18363, h18368, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18370 | h18370
                        · linarith only [h0, h17362, h17828, h18348, h18363, h18370, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases h1bigk with h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c | h18372c
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [hlam, p18372_0]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h0, hlam, p18372_0]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h11385, hlam, p18372_0]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h12794, hlam, p18372_0]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h13812, hlam, p18372_0]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            rcases p18372_3 (m.d 0 1) (by simp) with h18378 | h18378
                            · linarith only [h18378, hlam, p18372_0]
                            · rcases p18372_3 (m.d 1 2) (by simp) with h18380 | h18380
                              · rcases p18372_3 (m.d 1 3) (by simp) with h18381 | h18381
                                · linarith only [h18347, h18381, hlam]
                                · linarith only [h11385, h18381, hlam]
                              · linarith only [h18380, hlam, p18372_0]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [hlam, p18372_0]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h0, h17362, h18348, h18350, hc01, hc12, hlam, hphi, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h0, h17362, h18348, hc01, hc12, hlam, hphi, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h0, h17362, h18348, h18350, h18351, hc01, hc12, hlam, hphi, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h18351, h18370, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h18347, hlam, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [hlam, p18372_0]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h0, h17362, h18348, hc01, hc13, hlam, hphi, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h18351, hlam, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h18350, h18351, h18370, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h18348, hlam, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h18350, hlam, p18372_0]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [hlam, p18372_0]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h18363, hlam, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            rcases p18372_3 (m.d 0 1) (by simp) with h18399 | h18399
                            · linarith only [h18399, hlam, p18372_0]
                            · rcases p18372_3 (m.d 1 2) (by simp) with h18401 | h18401
                              · rcases p18372_3 (m.d 1 3) (by simp) with h18402 | h18402
                                · linarith only [h18351, h18402, hlam]
                                · linarith only [h11385, h18402, hlam]
                              · linarith only [h0, h18401, hlam]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h18349, hlam, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h11385, h18351, h18370, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [h0, h17362, h18348, h18351, h18370, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p18372_1]
                          · have p18372_0 := h18372c.1
                            have p18372_1 := h18372c.2.1
                            have p18372_2 := h18372c.2.2.1
                            have p18372_3 := h18372c.2.2.2
                            linarith only [hlam, p18372_0]
                  · linarith only [h14856, h17828, h18365, hlam]
            · linarith only [h11385, h14856, h17828, h18350, hc01, hc23, hlam, hphi, ht12]
          · linarith only [h0, h14856, h18347, h18349, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h14856, h18347, h18348, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h18414 | h18414
        · linarith only [h0, h17362, h18347, h18414, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h18416 | h18416
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18417 | h18417
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18418 | h18418
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18419 | h18419
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18420 | h18420
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18421 | h18421
                    · linarith only [h17828, h17829, h18414, h18416, h18420, h18421, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h18414, h18416, h18418, h18420, h18421, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h17828, h17829, h18347, h18414, h18416, h18418, h18420, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h17828, h17829, h18414, h18416, h18418, h18419, hc34, hc45, hlam, hphi]
              · linarith only [h18414, h18416, h18417, h18418, hlam]
            · linarith only [h11385, h17828, h18417, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18428 | h18428
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18429 | h18429
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18430 | h18430
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18431 | h18431
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18432 | h18432
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18433 | h18433
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18434 | h18434
                        · linarith only [h0, h17362, h17828, h17829, h18345, h18429, h18434, hc01, hc13, hlam, hphi]
                        · rcases h1bigk with h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c | h18436c
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h0, hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h11385, hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h12794, hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h13812, hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h18416, hc01, hc25, hlam, hphi, ht12, p18436_1]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h18347, hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h18414, hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h18416, hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            rcases p18436_3 (m.d 0 1) (by simp) with h18447 | h18447
                            · linarith only [h18447, hlam, p18436_0]
                            · rcases p18436_3 (m.d 1 2) (by simp) with h18449 | h18449
                              · linarith only [h18347, h18449, hlam]
                              · linarith only [h0, h18449, hlam]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h0, h18347, hc01, hc23, hlam, hphi, ht12, p18436_1]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h17829, h18347, h18430, h18434, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p18436_1]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h17828, h17829, h18347, h18430, h18434, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p18436_1]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            rcases p18436_3 (m.d 0 1) (by simp) with h18456 | h18456
                            · linarith only [h18456, hlam, p18436_0]
                            · rcases p18436_3 (m.d 1 2) (by simp) with h18458 | h18458
                              · linarith only [h18414, h18458, hlam]
                              · linarith only [h0, h18458, hlam]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p18436_1]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h18428, hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h17828, h17829, h18414, h18430, h18431, h18434, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p18436_1]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            rcases p18436_3 (m.d 0 1) (by simp) with h18465 | h18465
                            · linarith only [h18465, hlam, p18436_0]
                            · rcases p18436_3 (m.d 1 2) (by simp) with h18467 | h18467
                              · linarith only [h18416, h18467, hlam]
                              · linarith only [h0, h18467, hlam]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p18436_1]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h18429, hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [h18430, hlam, p18436_0]
                          · have p18436_0 := h18436c.1
                            have p18436_1 := h18436c.2.1
                            have p18436_2 := h18436c.2.2.1
                            have p18436_3 := h18436c.2.2.2
                            linarith only [hlam, p18436_0]
                      · linarith only [h0, h18414, h18433, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h18347, h18432, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h17828, h17829, h18347, h18429, h18431, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18477 | h18477
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18478 | h18478
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18479 | h18479
                      · linarith only [h0, h18414, h18430, h18479, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h18414, h18479, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h14856, h18429, h18478, hc01, hc13, hlam, hphi]
                  · linarith only [h11385, h17828, h18347, h18477, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18484 | h18484
                · linarith only [h12794, h18345, h18428, h18429, h18484, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18486 | h18486
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18487 | h18487
                    · linarith only [h11385, h18429, h18487, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h18347, h18487, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h17828, h18347, h18486, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
            · linarith only [h11385, h17828, h18428, hlam]

end R2N4
