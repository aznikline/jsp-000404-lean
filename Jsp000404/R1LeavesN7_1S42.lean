import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h27842 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  rcases m.htr 0 4 5 (by decide) (by decide) with h27843 | h27843
  · rcases m.htr 1 2 3 (by decide) (by decide) with h27844 | h27844
    · rcases m.htr 1 2 4 (by decide) (by decide) with h27845 | h27845
      · rcases m.htr 1 2 5 (by decide) (by decide) with h27846 | h27846
        · rcases m.htr 1 3 4 (by decide) (by decide) with h27847 | h27847
          · rcases m.htr 1 3 5 (by decide) (by decide) with h27848 | h27848
            · rcases m.htr 1 4 5 (by decide) (by decide) with h27849 | h27849
              · rcases m.htr 2 3 4 (by decide) (by decide) with h27850 | h27850
                · linarith only [h22350, h22353, h27842, h27850, hc02, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h27852 | h27852
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h27853 | h27853
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h27854 | h27854
                      · rcases h0bigk with h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c | h27855c
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [hlam, p27855_0]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h0, hlam, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h15532, hlam, p27855_0]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h18443, hlam, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h20697, hlam, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          rcases p27855_3 (m.d 0 1) (by simp) with h27861 | h27861
                          · linarith only [h0, h27861, hlam]
                          · rcases p27855_3 (m.d 0 2) (by simp) with h27863 | h27863
                            · rcases p27855_3 (m.d 0 3) (by simp) with h27864 | h27864
                              · linarith only [h22350, h27864, hlam]
                              · linarith only [h15532, h27864, hlam]
                            · linarith only [h0, h27863, hlam]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [hlam, p27855_0]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          rcases p27855_3 (m.d 0 1) (by simp) with h27869 | h27869
                          · linarith only [h0, h27869, hlam]
                          · rcases p27855_3 (m.d 0 2) (by simp) with h27871 | h27871
                            · rcases p27855_3 (m.d 0 3) (by simp) with h27872 | h27872
                              · linarith only [h22350, h27872, hlam]
                              · rcases p27855_3 (m.d 0 4) (by simp) with h27874 | h27874
                                · linarith only [h22351, h27874, hlam]
                                · linarith only [h22353, h27874, hlam]
                            · linarith only [h22350, h27871, hlam]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          rcases p27855_3 (m.d 0 1) (by simp) with h27878 | h27878
                          · linarith only [h0, h27878, hlam]
                          · rcases p27855_3 (m.d 0 2) (by simp) with h27880 | h27880
                            · rcases p27855_3 (m.d 0 3) (by simp) with h27881 | h27881
                              · linarith only [h22350, h27881, hlam]
                              · rcases p27855_3 (m.d 0 4) (by simp) with h27883 | h27883
                                · linarith only [h22351, h27883, hlam]
                                · rcases p27855_3 (m.d 0 5) (by simp) with h27885 | h27885
                                  · linarith only [h22352, h27885, hlam]
                                  · rcases h2bigk with h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c | h27887c
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h0, hlam, p27887_1]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      rcases p27887_3 (m.d 0 2) (by simp) with h27890 | h27890
                                      · rcases p27887_3 (m.d 1 2) (by simp) with h27891 | h27891
                                        · rcases p27887_3 (m.d 2 3) (by simp) with h27892 | h27892
                                          · linarith only [h27892, hlam, p27887_0]
                                          · rcases p27887_3 (m.d 2 4) (by simp) with h27894 | h27894
                                            · linarith only [h22351, h27894, hlam]
                                            · linarith only [h27850, h27894, hlam]
                                        · linarith only [h27844, h27891, hlam]
                                      · linarith only [h27890, hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      rcases p27887_3 (m.d 0 2) (by simp) with h27899 | h27899
                                      · rcases p27887_3 (m.d 1 2) (by simp) with h27900 | h27900
                                        · rcases p27887_3 (m.d 2 3) (by simp) with h27901 | h27901
                                          · linarith only [h22350, h27901, hlam]
                                          · rcases p27887_3 (m.d 2 4) (by simp) with h27903 | h27903
                                            · linarith only [h27903, hlam, p27887_0]
                                            · rcases p27887_3 (m.d 2 5) (by simp) with h27905 | h27905
                                              · linarith only [h22352, h27905, hlam]
                                              · rcases h3bigk with h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c | h27907c
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h15532, hlam, p27907_1]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h22353, h27847, h27852, h27854, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p27907_1]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h22353, hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h0, h22353, h27854, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p27855_1, p27907_1]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  rcases p27907_3 (m.d 0 3) (by simp) with h27913 | h27913
                                                  · linarith only [h15532, h27913, hlam]
                                                  · rcases p27907_3 (m.d 1 3) (by simp) with h27915 | h27915
                                                    · rcases p27907_3 (m.d 2 3) (by simp) with h27916 | h27916
                                                      · linarith only [h27844, h27916, hlam]
                                                      · rcases p27907_3 (m.d 3 4) (by simp) with h27918 | h27918
                                                        · linarith only [h27847, h27918, hlam]
                                                        · linarith only [h22353, h27918, hlam]
                                                    · linarith only [h15532, h27915, hlam]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  rcases p27907_3 (m.d 0 3) (by simp) with h27923 | h27923
                                                  · linarith only [h15532, h27923, hlam]
                                                  · linarith only [h22350, h27923, hlam]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h15532, h22353, h27844, hc01, hc12, hlam, hphi, p27907_1]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h22353, h27842, h27847, hlam, p27907_2]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h22350, hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h27844, hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h27850, hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h22350, h22353, h27847, h27854, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p27907_1]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h15532, h27847, hc01, hc13, hlam, hphi, p27907_1]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h27847, hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h27844, h27847, h27852, h27854, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p27907_1]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  rcases p27907_3 (m.d 0 3) (by simp) with h27937 | h27937
                                                  · linarith only [h22353, h27937, hlam]
                                                  · linarith only [h27842, h27937, hlam]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h27842, hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h27848, hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h27852, hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [h27854, hlam, p27907_0]
                                                · have p27907_0 := h27907c.1
                                                  have p27907_1 := h27907c.2.1
                                                  have p27907_2 := h27907c.2.2.1
                                                  have p27907_3 := h27907c.2.2.2
                                                  linarith only [hlam, p27907_0]
                                        · linarith only [h27845, h27900, hlam]
                                      · linarith only [h27899, hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      rcases p27887_3 (m.d 0 2) (by simp) with h27947 | h27947
                                      · rcases p27887_3 (m.d 1 2) (by simp) with h27948 | h27948
                                        · rcases p27887_3 (m.d 2 3) (by simp) with h27949 | h27949
                                          · linarith only [h22350, h27949, hlam]
                                          · linarith only [h27852, h27949, hlam]
                                        · linarith only [h27846, h27948, hlam]
                                      · linarith only [h27947, hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p27855_1, p27887_1]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      rcases p27887_3 (m.d 0 2) (by simp) with h27956 | h27956
                                      · linarith only [h0, h27956, hlam]
                                      · linarith only [h22350, h27956, hlam]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      rcases p27887_3 (m.d 0 2) (by simp) with h27959 | h27959
                                      · linarith only [h0, h27959, hlam]
                                      · linarith only [h22351, h27959, hlam]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      rcases p27887_3 (m.d 0 2) (by simp) with h27962 | h27962
                                      · linarith only [h0, h27962, hlam]
                                      · linarith only [h22352, h27962, hlam]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h22350, hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h27844, hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h27850, hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h22350, h22353, hc02, hc25, hlam, hphi, ht0b, ht5b, p27855_1, p27887_1]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h22351, hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h27845, hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h0, h22351, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p27855_1, p27887_1]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h0, h22351, h27852, h27854, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p27855_1, p27887_1]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h22352, hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h27846, hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h27852, hlam, p27887_1]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [h27853, hlam, p27887_0]
                                    · have p27887_0 := h27887c.1
                                      have p27887_1 := h27887c.2.1
                                      have p27887_2 := h27887c.2.2.1
                                      have p27887_3 := h27887c.2.2.2
                                      linarith only [hlam, p27887_0]
                            · linarith only [h22351, h27880, hlam]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          rcases p27855_3 (m.d 0 1) (by simp) with h27981 | h27981
                          · linarith only [h0, h27981, hlam]
                          · rcases p27855_3 (m.d 0 2) (by simp) with h27983 | h27983
                            · rcases p27855_3 (m.d 0 3) (by simp) with h27984 | h27984
                              · linarith only [h22350, h27984, hlam]
                              · linarith only [h27842, h27984, hlam]
                            · linarith only [h22352, h27983, hlam]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h22353, h27844, h27847, hc01, hc12, hlam, hphi, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h22350, hlam, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [hlam, p27855_0]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h22353, hlam, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h20697, h22353, h27844, h27847, hc01, hc12, hlam, hphi, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h22353, h27844, h27847, hc01, hc12, hlam, hphi, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h22351, hlam, p27855_0]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h15532, h22353, h27844, h27847, hc01, hc12, hlam, hphi, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [hlam, p27855_0]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h20697, h22353, h27844, h27847, hc01, hc12, hlam, hphi, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h22353, h27842, h27844, h27847, hc01, hc12, hlam, hphi, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h22352, hlam, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h27842, hlam, p27855_0]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [h27843, hlam, p27855_1]
                        · have p27855_0 := h27855c.1
                          have p27855_1 := h27855c.2.1
                          have p27855_2 := h27855c.2.2.1
                          have p27855_3 := h27855c.2.2.2
                          linarith only [hlam, p27855_0]
                      · linarith only [h22353, h27843, h27854, hlam]
                    · linarith only [h22353, h27842, h27843, h27847, h27850, h27852, h27853, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h22353, h27842, h27844, h27847, h27852, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h22353, h27842, h27843, h27847, h27849, hlam]
            · linarith only [h22353, h27842, h27847, h27848, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h28008 | h28008
            · rcases m.htr 1 4 5 (by decide) (by decide) with h28009 | h28009
              · rcases m.htr 2 3 4 (by decide) (by decide) with h28010 | h28010
                · linarith only [h15532, h27847, h28010, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h28012 | h28012
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h28013 | h28013
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h28014 | h28014
                      · rcases h0bigk with h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c | h28015c
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [hlam, p28015_0]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h0, hlam, p28015_1]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h15532, hlam, p28015_0]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h18443, hlam, p28015_1]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h20697, hlam, p28015_1]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          rcases p28015_3 (m.d 0 1) (by simp) with h28021 | h28021
                          · linarith only [h0, h28021, hlam]
                          · rcases p28015_3 (m.d 0 2) (by simp) with h28023 | h28023
                            · rcases p28015_3 (m.d 0 3) (by simp) with h28024 | h28024
                              · linarith only [h22350, h28024, hlam]
                              · linarith only [h15532, h28024, hlam]
                            · linarith only [h0, h28023, hlam]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [hlam, p28015_0]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          rcases p28015_3 (m.d 0 1) (by simp) with h28029 | h28029
                          · linarith only [h0, h28029, hlam]
                          · rcases p28015_3 (m.d 0 2) (by simp) with h28031 | h28031
                            · rcases p28015_3 (m.d 0 3) (by simp) with h28032 | h28032
                              · linarith only [h22350, h28032, hlam]
                              · rcases p28015_3 (m.d 0 4) (by simp) with h28034 | h28034
                                · linarith only [h22351, h28034, hlam]
                                · linarith only [h22353, h28034, hlam]
                            · linarith only [h22350, h28031, hlam]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          rcases p28015_3 (m.d 0 1) (by simp) with h28038 | h28038
                          · linarith only [h0, h28038, hlam]
                          · rcases p28015_3 (m.d 0 2) (by simp) with h28040 | h28040
                            · rcases p28015_3 (m.d 0 3) (by simp) with h28041 | h28041
                              · linarith only [h22350, h28041, hlam]
                              · rcases p28015_3 (m.d 0 4) (by simp) with h28043 | h28043
                                · linarith only [h22351, h28043, hlam]
                                · rcases p28015_3 (m.d 0 5) (by simp) with h28045 | h28045
                                  · linarith only [h22352, h28045, hlam]
                                  · rcases h2bigk with h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c | h28047c
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h0, hlam, p28047_1]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      rcases p28047_3 (m.d 0 2) (by simp) with h28050 | h28050
                                      · rcases p28047_3 (m.d 1 2) (by simp) with h28051 | h28051
                                        · rcases p28047_3 (m.d 2 3) (by simp) with h28052 | h28052
                                          · linarith only [h28052, hlam, p28047_0]
                                          · rcases p28047_3 (m.d 2 4) (by simp) with h28054 | h28054
                                            · linarith only [h22351, h28054, hlam]
                                            · linarith only [h28010, h28054, hlam]
                                        · linarith only [h27844, h28051, hlam]
                                      · linarith only [h28050, hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      rcases p28047_3 (m.d 0 2) (by simp) with h28059 | h28059
                                      · rcases p28047_3 (m.d 1 2) (by simp) with h28060 | h28060
                                        · rcases p28047_3 (m.d 2 3) (by simp) with h28061 | h28061
                                          · linarith only [h22350, h28061, hlam]
                                          · rcases p28047_3 (m.d 2 4) (by simp) with h28063 | h28063
                                            · linarith only [h28063, hlam, p28047_0]
                                            · rcases p28047_3 (m.d 2 5) (by simp) with h28065 | h28065
                                              · linarith only [h22352, h28065, hlam]
                                              · rcases h3bigk with h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c | h28067c
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h15532, hlam, p28067_1]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h15532, h27847, h28012, h28014, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p28067_1]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h22353, hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h0, h22353, h28014, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p28015_1, p28067_1]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h27847, hc03, hc34, hlam, hphi, p28067_1]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h27847, h28012, h28014, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p28067_1]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h27847, hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  rcases p28067_3 (m.d 0 3) (by simp) with h28077 | h28077
                                                  · linarith only [h15532, h28077, hlam]
                                                  · linarith only [h27842, h28077, hlam]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h22350, hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h27844, hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h28010, hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h0, h28010, h28014, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p28047_1, p28067_1]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  rcases p28067_3 (m.d 0 3) (by simp) with h28085 | h28085
                                                  · linarith only [h28085, hlam, p28067_0]
                                                  · rcases p28067_3 (m.d 1 3) (by simp) with h28087 | h28087
                                                    · linarith only [h27847, h28087, hlam]
                                                    · linarith only [h15532, h28087, hlam]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h15532, hc01, hc34, hlam, hphi, ht12, ht23, p28067_1]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  rcases p28067_3 (m.d 0 3) (by simp) with h28091 | h28091
                                                  · linarith only [h22353, h28091, hlam]
                                                  · linarith only [h22350, h28091, hlam]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  rcases p28067_3 (m.d 0 3) (by simp) with h28095 | h28095
                                                  · linarith only [h22353, h28095, hlam]
                                                  · linarith only [h27842, h28095, hlam]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h27842, hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h28008, hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h28012, hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [h28014, hlam, p28067_0]
                                                · have p28067_0 := h28067c.1
                                                  have p28067_1 := h28067c.2.1
                                                  have p28067_2 := h28067c.2.2.1
                                                  have p28067_3 := h28067c.2.2.2
                                                  linarith only [hlam, p28067_0]
                                        · linarith only [h27845, h28060, hlam]
                                      · linarith only [h28059, hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      rcases p28047_3 (m.d 0 2) (by simp) with h28105 | h28105
                                      · rcases p28047_3 (m.d 1 2) (by simp) with h28106 | h28106
                                        · rcases p28047_3 (m.d 2 3) (by simp) with h28107 | h28107
                                          · linarith only [h22350, h28107, hlam]
                                          · linarith only [h28012, h28107, hlam]
                                        · linarith only [h27846, h28106, hlam]
                                      · linarith only [h28105, hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h22353, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p28015_1, p28047_1]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      rcases p28047_3 (m.d 0 2) (by simp) with h28114 | h28114
                                      · linarith only [h0, h28114, hlam]
                                      · linarith only [h22350, h28114, hlam]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      rcases p28047_3 (m.d 0 2) (by simp) with h28117 | h28117
                                      · linarith only [h0, h28117, hlam]
                                      · linarith only [h22351, h28117, hlam]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      rcases p28047_3 (m.d 0 2) (by simp) with h28120 | h28120
                                      · linarith only [h0, h28120, hlam]
                                      · linarith only [h22352, h28120, hlam]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h22350, hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h27844, hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h28010, hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h22351, h28010, hc02, hc25, hlam, hphi, ht0b, ht5b, p28015_1, p28047_1]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h22351, hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h27845, hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h22351, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28015_1, p28047_1]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h0, h22351, h28012, h28014, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p28015_1, p28047_1]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h22352, hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h27846, hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h28012, hlam, p28047_1]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [h28013, hlam, p28047_0]
                                    · have p28047_0 := h28047c.1
                                      have p28047_1 := h28047c.2.1
                                      have p28047_2 := h28047c.2.2.1
                                      have p28047_3 := h28047c.2.2.2
                                      linarith only [hlam, p28047_0]
                            · linarith only [h22351, h28040, hlam]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          rcases p28015_3 (m.d 0 1) (by simp) with h28139 | h28139
                          · linarith only [h0, h28139, hlam]
                          · rcases p28015_3 (m.d 0 2) (by simp) with h28141 | h28141
                            · rcases p28015_3 (m.d 0 3) (by simp) with h28142 | h28142
                              · linarith only [h22350, h28142, hlam]
                              · linarith only [h27842, h28142, hlam]
                            · linarith only [h22352, h28141, hlam]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h22353, hc01, hc34, hlam, hphi, ht12, ht23, p28015_1]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h22350, hlam, p28015_1]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [hlam, p28015_0]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h22353, hlam, p28015_1]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h20697, h22353, hc01, hc34, hlam, hphi, ht12, ht23, p28015_1]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          rcases p28015_3 (m.d 0 1) (by simp) with h28151 | h28151
                          · linarith only [h18443, h28151, hlam]
                          · rcases p28015_3 (m.d 0 2) (by simp) with h28153 | h28153
                            · rcases p28015_3 (m.d 0 3) (by simp) with h28154 | h28154
                              · linarith only [h22353, h28154, hlam]
                              · linarith only [h15532, h28154, hlam]
                            · linarith only [h0, h28153, hlam]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h22351, hlam, p28015_0]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          rcases p28015_3 (m.d 0 1) (by simp) with h28159 | h28159
                          · linarith only [h18443, h28159, hlam]
                          · rcases p28015_3 (m.d 0 2) (by simp) with h28161 | h28161
                            · rcases p28015_3 (m.d 0 3) (by simp) with h28162 | h28162
                              · linarith only [h22353, h28162, hlam]
                              · rcases p28015_3 (m.d 0 4) (by simp) with h28164 | h28164
                                · rcases p28015_3 (m.d 0 5) (by simp) with h28165 | h28165
                                  · linarith only [h27843, h28165, hlam]
                                  · rcases h2bigk with h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c | h28167c
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h0, hlam, p28167_1]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      rcases p28167_3 (m.d 0 2) (by simp) with h28170 | h28170
                                      · rcases p28167_3 (m.d 1 2) (by simp) with h28171 | h28171
                                        · rcases p28167_3 (m.d 2 3) (by simp) with h28172 | h28172
                                          · linarith only [h28172, hlam, p28167_0]
                                          · rcases p28167_3 (m.d 2 4) (by simp) with h28174 | h28174
                                            · linarith only [h22351, h28174, hlam]
                                            · linarith only [h28010, h28174, hlam]
                                        · linarith only [h27844, h28171, hlam]
                                      · linarith only [h28170, hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      rcases p28167_3 (m.d 0 2) (by simp) with h28179 | h28179
                                      · rcases p28167_3 (m.d 1 2) (by simp) with h28180 | h28180
                                        · rcases p28167_3 (m.d 2 3) (by simp) with h28181 | h28181
                                          · linarith only [h22350, h28181, hlam]
                                          · rcases p28167_3 (m.d 2 4) (by simp) with h28183 | h28183
                                            · linarith only [h28183, hlam, p28167_0]
                                            · rcases p28167_3 (m.d 2 5) (by simp) with h28185 | h28185
                                              · linarith only [h22352, h28185, hlam]
                                              · rcases h3bigk with h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c | h28187c
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h15532, hlam, p28187_1]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h18443, h27847, h28012, h28014, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p28015_1, p28187_1]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h22353, hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h18443, h27847, h28014, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p28015_1, p28187_1]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h27847, hc03, hc34, hlam, hphi, p28187_1]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h27847, h28012, h28014, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p28187_1]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h27847, hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  rcases p28187_3 (m.d 0 3) (by simp) with h28197 | h28197
                                                  · linarith only [h15532, h28197, hlam]
                                                  · linarith only [h27842, h28197, hlam]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h22350, hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h27844, hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h28010, hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h18443, h22350, h27847, h28014, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p28015_1, p28187_1]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  rcases p28187_3 (m.d 0 3) (by simp) with h28205 | h28205
                                                  · linarith only [h28205, hlam, p28187_0]
                                                  · rcases p28187_3 (m.d 1 3) (by simp) with h28207 | h28207
                                                    · linarith only [h27847, h28207, hlam]
                                                    · linarith only [h15532, h28207, hlam]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h15532, hc01, hc34, hlam, hphi, ht12, ht23, p28187_1]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  rcases p28187_3 (m.d 0 3) (by simp) with h28211 | h28211
                                                  · linarith only [h22353, h28211, hlam]
                                                  · linarith only [h22350, h28211, hlam]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h18443, h27842, h27847, hlam, p28015_1, p28187_2]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h27842, hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h28008, hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h28012, hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [h28014, hlam, p28187_0]
                                                · have p28187_0 := h28187c.1
                                                  have p28187_1 := h28187c.2.1
                                                  have p28187_2 := h28187c.2.2.1
                                                  have p28187_3 := h28187c.2.2.2
                                                  linarith only [hlam, p28187_0]
                                        · linarith only [h27845, h28180, hlam]
                                      · linarith only [h28179, hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      rcases p28167_3 (m.d 0 2) (by simp) with h28223 | h28223
                                      · rcases p28167_3 (m.d 1 2) (by simp) with h28224 | h28224
                                        · rcases p28167_3 (m.d 2 3) (by simp) with h28225 | h28225
                                          · linarith only [h22350, h28225, hlam]
                                          · linarith only [h28012, h28225, hlam]
                                        · linarith only [h27846, h28224, hlam]
                                      · linarith only [h28223, hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h22350, h28012, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p28167_1]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      rcases p28167_3 (m.d 0 2) (by simp) with h28232 | h28232
                                      · linarith only [h0, h28232, hlam]
                                      · linarith only [h22350, h28232, hlam]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      rcases p28167_3 (m.d 0 2) (by simp) with h28235 | h28235
                                      · linarith only [h0, h28235, hlam]
                                      · linarith only [h22351, h28235, hlam]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      rcases p28167_3 (m.d 0 2) (by simp) with h28238 | h28238
                                      · linarith only [h0, h28238, hlam]
                                      · linarith only [h22352, h28238, hlam]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h22350, hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h27844, hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h28010, hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h18443, h22350, h27847, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p28015_1, p28167_1]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h22351, hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h27845, hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h22351, h28012, h28014, hc02, hc45, hlam, hphi, ht0b, ht5b, p28167_1]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      rcases p28167_3 (m.d 0 2) (by simp) with h28250 | h28250
                                      · rcases p28167_3 (m.d 1 2) (by simp) with h28251 | h28251
                                        · rcases p28167_3 (m.d 2 3) (by simp) with h28252 | h28252
                                          · linarith only [h28010, h28252, hlam]
                                          · linarith only [h28012, h28252, hlam]
                                        · linarith only [h27846, h28251, hlam]
                                      · linarith only [h22352, h28250, hlam]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h22352, hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h27846, hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h28012, hlam, p28167_1]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [h28013, hlam, p28167_0]
                                    · have p28167_0 := h28167c.1
                                      have p28167_1 := h28167c.2.1
                                      have p28167_2 := h28167c.2.2.1
                                      have p28167_3 := h28167c.2.2.2
                                      linarith only [hlam, p28167_0]
                                · linarith only [h22353, h28164, hlam]
                            · linarith only [h22350, h28161, hlam]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [hlam, p28015_0]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          rcases p28015_3 (m.d 0 1) (by simp) with h28265 | h28265
                          · linarith only [h18443, h28265, hlam]
                          · rcases p28015_3 (m.d 0 2) (by simp) with h28267 | h28267
                            · rcases p28015_3 (m.d 0 3) (by simp) with h28268 | h28268
                              · linarith only [h22353, h28268, hlam]
                              · linarith only [h27842, h28268, hlam]
                            · linarith only [h22352, h28267, hlam]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h22353, h27842, hc01, hc34, hlam, hphi, ht12, ht23, p28015_1]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h22352, hlam, p28015_1]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h27842, hlam, p28015_0]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [h27843, hlam, p28015_1]
                        · have p28015_0 := h28015c.1
                          have p28015_1 := h28015c.2.1
                          have p28015_2 := h28015c.2.2.1
                          have p28015_3 := h28015c.2.2.2
                          linarith only [hlam, p28015_0]
                      · linarith only [h15532, h27847, h28014, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h28010, h28012, h28013, hlam]
                  · linarith only [h15532, h27842, h27847, h28012, hc23, hc34, hlam, hphi]
              · linarith only [h18443, h20697, h27843, h27847, h28008, h28009, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h15532, h27842, h28008, hlam]
        · linarith only [h0, h22352, h27846, hlam]
      · linarith only [h0, h22351, h27845, hlam]
    · linarith only [h0, h22350, h27844, hlam]
  · linarith only [h22353, h27842, h27843, hlam]

set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h27842 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28286 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h28287 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h28288 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h28289 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h28290 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  rcases m.htr 1 3 5 (by decide) (by decide) with h28291 | h28291
  · rcases m.htr 1 4 5 (by decide) (by decide) with h28292 | h28292
    · rcases m.htr 2 3 4 (by decide) (by decide) with h28293 | h28293
      · linarith only [h0, h15532, h22350, h22353, h28293, hc01, hc12, hlam, hphi]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h28295 | h28295
        · linarith only [h22350, h27842, h28295, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h28297 | h28297
          · rcases m.htr 3 4 5 (by decide) (by decide) with h28298 | h28298
            · rcases h0bigk with h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c | h28299c
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [hlam, p28299_0]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h0, hlam, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h15532, hlam, p28299_0]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h18443, hlam, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h20697, hlam, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                rcases p28299_3 (m.d 0 1) (by simp) with h28305 | h28305
                · linarith only [h0, h28305, hlam]
                · rcases p28299_3 (m.d 0 2) (by simp) with h28307 | h28307
                  · rcases p28299_3 (m.d 0 3) (by simp) with h28308 | h28308
                    · linarith only [h22350, h28308, hlam]
                    · linarith only [h15532, h28308, hlam]
                  · linarith only [h0, h28307, hlam]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [hlam, p28299_0]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                rcases p28299_3 (m.d 0 1) (by simp) with h28313 | h28313
                · linarith only [h0, h28313, hlam]
                · rcases p28299_3 (m.d 0 2) (by simp) with h28315 | h28315
                  · rcases p28299_3 (m.d 0 3) (by simp) with h28316 | h28316
                    · linarith only [h22350, h28316, hlam]
                    · rcases p28299_3 (m.d 0 4) (by simp) with h28318 | h28318
                      · linarith only [h22351, h28318, hlam]
                      · linarith only [h22353, h28318, hlam]
                  · linarith only [h22350, h28315, hlam]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                rcases p28299_3 (m.d 0 1) (by simp) with h28322 | h28322
                · linarith only [h0, h28322, hlam]
                · rcases p28299_3 (m.d 0 2) (by simp) with h28324 | h28324
                  · rcases p28299_3 (m.d 0 3) (by simp) with h28325 | h28325
                    · linarith only [h22350, h28325, hlam]
                    · rcases p28299_3 (m.d 0 4) (by simp) with h28327 | h28327
                      · linarith only [h22351, h28327, hlam]
                      · rcases p28299_3 (m.d 0 5) (by simp) with h28329 | h28329
                        · linarith only [h22352, h28329, hlam]
                        · rcases h2bigk with h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c | h28331c
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h0, hlam, p28331_1]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            rcases p28331_3 (m.d 0 2) (by simp) with h28334 | h28334
                            · rcases p28331_3 (m.d 1 2) (by simp) with h28335 | h28335
                              · rcases p28331_3 (m.d 2 3) (by simp) with h28336 | h28336
                                · linarith only [h28336, hlam, p28331_0]
                                · rcases p28331_3 (m.d 2 4) (by simp) with h28338 | h28338
                                  · linarith only [h22351, h28338, hlam]
                                  · linarith only [h28293, h28338, hlam]
                              · linarith only [h28287, h28335, hlam]
                            · linarith only [h28334, hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            rcases p28331_3 (m.d 0 2) (by simp) with h28343 | h28343
                            · rcases p28331_3 (m.d 1 2) (by simp) with h28344 | h28344
                              · rcases p28331_3 (m.d 2 3) (by simp) with h28345 | h28345
                                · linarith only [h22350, h28345, hlam]
                                · rcases p28331_3 (m.d 2 4) (by simp) with h28347 | h28347
                                  · linarith only [h28347, hlam, p28331_0]
                                  · rcases p28331_3 (m.d 2 5) (by simp) with h28349 | h28349
                                    · linarith only [h22352, h28349, hlam]
                                    · rcases h3bigk with h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c | h28351c
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h15532, hlam, p28351_1]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h27842, hc23, hc35, hlam, hphi, p28351_1]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h22353, hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h27842, hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        rcases p28351_3 (m.d 0 3) (by simp) with h28357 | h28357
                                        · linarith only [h15532, h28357, hlam]
                                        · rcases p28351_3 (m.d 1 3) (by simp) with h28359 | h28359
                                          · rcases p28351_3 (m.d 2 3) (by simp) with h28360 | h28360
                                            · linarith only [h28287, h28360, hlam]
                                            · rcases p28351_3 (m.d 3 4) (by simp) with h28362 | h28362
                                              · linarith only [h28290, h28362, hlam]
                                              · linarith only [h22353, h28362, hlam]
                                          · linarith only [h15532, h28359, hlam]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        rcases p28351_3 (m.d 0 3) (by simp) with h28367 | h28367
                                        · linarith only [h15532, h28367, hlam]
                                        · linarith only [h22350, h28367, hlam]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h15532, h22353, h28287, hc01, hc12, hlam, hphi, p28351_1]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h15532, h27842, h28287, hc01, hc12, hlam, hphi, p28351_1]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h22350, hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h28287, hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h28293, hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h28295, hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h15532, h28287, h28290, hc01, hc12, hlam, hphi, p28351_1]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h28290, hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        rcases p28351_3 (m.d 0 3) (by simp) with h28379 | h28379
                                        · linarith only [h22353, h28379, hlam]
                                        · linarith only [h22350, h28379, hlam]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h15532, h27842, h28287, h28290, hc01, hc12, hlam, hphi, p28351_1]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h15532, h28287, h28291, hc01, hc12, hlam, hphi, p28351_1]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h28291, hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        rcases p28351_3 (m.d 0 3) (by simp) with h28386 | h28386
                                        · linarith only [h27842, h28386, hlam]
                                        · linarith only [h22350, h28386, hlam]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [h28298, hlam, p28351_0]
                                      · have p28351_0 := h28351c.1
                                        have p28351_1 := h28351c.2.1
                                        have p28351_2 := h28351c.2.2.1
                                        have p28351_3 := h28351c.2.2.2
                                        linarith only [hlam, p28351_0]
                              · linarith only [h28288, h28344, hlam]
                            · linarith only [h28343, hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            rcases p28331_3 (m.d 0 2) (by simp) with h28393 | h28393
                            · rcases p28331_3 (m.d 1 2) (by simp) with h28394 | h28394
                              · rcases p28331_3 (m.d 2 3) (by simp) with h28395 | h28395
                                · linarith only [h22350, h28395, hlam]
                                · rcases p28331_3 (m.d 2 4) (by simp) with h28397 | h28397
                                  · linarith only [h22351, h28397, hlam]
                                  · linarith only [h28297, h28397, hlam]
                              · linarith only [h28289, h28394, hlam]
                            · linarith only [h28393, hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p28299_1, p28331_1]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            rcases p28331_3 (m.d 0 2) (by simp) with h28404 | h28404
                            · linarith only [h0, h28404, hlam]
                            · linarith only [h22350, h28404, hlam]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            rcases p28331_3 (m.d 0 2) (by simp) with h28407 | h28407
                            · linarith only [h0, h28407, hlam]
                            · linarith only [h22351, h28407, hlam]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            rcases p28331_3 (m.d 0 2) (by simp) with h28410 | h28410
                            · linarith only [h0, h28410, hlam]
                            · linarith only [h22352, h28410, hlam]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h22350, hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h28287, hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h28293, hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h28295, hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h22351, hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h28288, hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h22351, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28299_1, p28331_1]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h0, h22351, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p28299_1, p28331_1]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h22352, hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h28289, hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h0, h22352, h28286, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p28299_1, p28331_1]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [h28297, hlam, p28331_0]
                          · have p28331_0 := h28331c.1
                            have p28331_1 := h28331c.2.1
                            have p28331_2 := h28331c.2.2.1
                            have p28331_3 := h28331c.2.2.2
                            linarith only [hlam, p28331_0]
                  · linarith only [h22351, h28324, hlam]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                rcases p28299_3 (m.d 0 1) (by simp) with h28429 | h28429
                · linarith only [h0, h28429, hlam]
                · rcases p28299_3 (m.d 0 2) (by simp) with h28431 | h28431
                  · rcases p28299_3 (m.d 0 3) (by simp) with h28432 | h28432
                    · linarith only [h22350, h28432, hlam]
                    · rcases p28299_3 (m.d 0 4) (by simp) with h28434 | h28434
                      · linarith only [h22351, h28434, hlam]
                      · linarith only [h28286, h28434, hlam]
                  · linarith only [h22352, h28431, hlam]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h22353, h28287, h28290, hc01, hc12, hlam, hphi, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h22350, hlam, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [hlam, p28299_0]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h22353, hlam, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h27842, hlam, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h22353, h28287, h28290, hc01, hc12, hlam, hphi, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h22351, hlam, p28299_0]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h15532, h22353, h28287, h28290, hc01, hc12, hlam, hphi, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [hlam, p28299_0]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h20697, h22353, h28287, h28290, hc01, hc12, hlam, hphi, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h27842, h28287, h28290, h28298, hc01, hc12, hlam, hphi, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h22352, hlam, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h15532, h27842, h28287, h28290, h28298, hc01, hc12, hlam, hphi, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [h28286, hlam, p28299_1]
              · have p28299_0 := h28299c.1
                have p28299_1 := h28299c.2.1
                have p28299_2 := h28299c.2.2.1
                have p28299_3 := h28299c.2.2.2
                linarith only [hlam, p28299_0]
            · linarith only [h22353, h28286, h28298, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h28454 | h28454
            · rcases h0bigk with h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c | h28455c
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [hlam, p28455_0]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h0, hlam, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h15532, hlam, p28455_0]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h18443, hlam, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h20697, hlam, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                rcases p28455_3 (m.d 0 1) (by simp) with h28461 | h28461
                · linarith only [h0, h28461, hlam]
                · rcases p28455_3 (m.d 0 2) (by simp) with h28463 | h28463
                  · rcases p28455_3 (m.d 0 3) (by simp) with h28464 | h28464
                    · linarith only [h22350, h28464, hlam]
                    · linarith only [h15532, h28464, hlam]
                  · linarith only [h0, h28463, hlam]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [hlam, p28455_0]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                rcases p28455_3 (m.d 0 1) (by simp) with h28469 | h28469
                · linarith only [h0, h28469, hlam]
                · rcases p28455_3 (m.d 0 2) (by simp) with h28471 | h28471
                  · rcases p28455_3 (m.d 0 3) (by simp) with h28472 | h28472
                    · linarith only [h22350, h28472, hlam]
                    · rcases p28455_3 (m.d 0 4) (by simp) with h28474 | h28474
                      · linarith only [h22351, h28474, hlam]
                      · linarith only [h22353, h28474, hlam]
                  · linarith only [h22350, h28471, hlam]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h0, h28286, h28293, h28297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                rcases p28455_3 (m.d 0 1) (by simp) with h28479 | h28479
                · linarith only [h0, h28479, hlam]
                · rcases p28455_3 (m.d 0 2) (by simp) with h28481 | h28481
                  · rcases p28455_3 (m.d 0 3) (by simp) with h28482 | h28482
                    · linarith only [h22350, h28482, hlam]
                    · rcases p28455_3 (m.d 0 4) (by simp) with h28484 | h28484
                      · linarith only [h22351, h28484, hlam]
                      · linarith only [h28286, h28484, hlam]
                  · linarith only [h22352, h28481, hlam]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h22353, hc01, hc34, hlam, hphi, ht12, ht23, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h22350, hlam, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [hlam, p28455_0]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h22353, hlam, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h27842, hlam, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h22353, h28287, h28290, hc01, hc12, hlam, hphi, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h22351, hlam, p28455_0]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h15532, h22353, h28287, h28290, hc01, hc12, hlam, hphi, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [hlam, p28455_0]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h22353, h28286, h28287, h28290, h28293, h28297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h27842, h28287, h28290, h28454, hc01, hc12, hlam, hphi, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h22352, hlam, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h15532, h27842, h28287, h28290, h28454, hc01, hc12, hlam, hphi, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [h28286, hlam, p28455_1]
              · have p28455_0 := h28455c.1
                have p28455_1 := h28455c.2.1
                have p28455_2 := h28455c.2.2.1
                have p28455_3 := h28455c.2.2.2
                linarith only [hlam, p28455_0]
            · linarith only [h15532, h18443, h22353, h28286, h28287, h28290, h28454, hc01, hc12, hlam, hphi]
    · linarith only [h18443, h22353, h28286, h28287, h28290, h28292, hc01, hc12, hlam, hphi]
  · linarith only [h15532, h22353, h28290, h28291, hc01, hc35, hlam, hphi, ht12, ht23]

end R2N4
