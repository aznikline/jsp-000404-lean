import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_67S11

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_M_LI_L_I_L_0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h814 | h814
  · rcases m.htr 0 2 3 (by decide) (by decide) with h815 | h815
    · rcases m.htr 0 2 4 (by decide) (by decide) with h816 | h816
      · rcases m.htr 0 2 5 (by decide) (by decide) with h817 | h817
        · rcases m.htr 0 3 4 (by decide) (by decide) with h818 | h818
          · rcases m.htr 0 3 5 (by decide) (by decide) with h819 | h819
            · rcases m.htr 1 2 3 (by decide) (by decide) with h820 | h820
              · rcases m.htr 1 2 4 (by decide) (by decide) with h821 | h821
                · rcases m.htr 1 2 5 (by decide) (by decide) with h822 | h822
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h823 | h823
                    · linarith only [h0, h814, h823, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h814, h818, h820, h823, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h822, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h814, h820, h821, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h814, h820, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h818, h819, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h830 | h830
            · rcases m.htr 1 2 3 (by decide) (by decide) with h831 | h831
              · rcases m.htr 1 2 4 (by decide) (by decide) with h832 | h832
                · rcases m.htr 1 2 5 (by decide) (by decide) with h833 | h833
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h834 | h834
                    · linarith only [h0, h814, h818, h834, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h836 | h836
                      · linarith only [h0, h814, h836, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h818, h830, h836, hc13, hc34, hlam, hphi]
                  · linarith only [h0, h814, h831, h833, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h814, h831, h832, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h814, h831, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h842 | h842
              · rcases m.htr 1 2 4 (by decide) (by decide) with h843 | h843
                · rcases m.htr 1 2 5 (by decide) (by decide) with h844 | h844
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h845 | h845
                    · linarith only [h0, h814, h845, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h847 | h847
                      · linarith only [h0, h814, h830, h847, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h849 | h849
                        · linarith only [h814, h818, h842, h849, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h851 | h851
                          · linarith only [h814, h830, h842, h851, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h853 | h853
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h854 | h854
                              · rcases h2bigk with h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h0, hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  rcases p855_3 (m.d 0 2) (by simp) with h858 | h858
                                  · rcases p855_3 (m.d 1 2) (by simp) with h859 | h859
                                    · rcases p855_3 (m.d 2 3) (by simp) with h860 | h860
                                      · linarith only [h860, hlam, p855_0]
                                      · rcases p855_3 (m.d 2 4) (by simp) with h862 | h862
                                        · linarith only [h816, h862, hlam]
                                        · linarith only [h849, h862, hlam]
                                    · linarith only [h842, h859, hlam]
                                  · linarith only [h858, hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h0, h853, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p855_1, u2elo1]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  rcases p855_3 (m.d 0 2) (by simp) with h868 | h868
                                  · rcases p855_3 (m.d 1 2) (by simp) with h869 | h869
                                    · rcases p855_3 (m.d 2 3) (by simp) with h870 | h870
                                      · linarith only [h815, h870, hlam]
                                      · rcases p855_3 (m.d 2 4) (by simp) with h872 | h872
                                        · linarith only [h816, h872, hlam]
                                        · linarith only [h853, h872, hlam]
                                    · linarith only [h844, h869, hlam]
                                  · linarith only [h868, hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [hc02, hlam, hphi, p855_1, u2elo1]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  rcases p855_3 (m.d 0 2) (by simp) with h879 | h879
                                  · linarith only [h0, h879, hlam]
                                  · linarith only [h815, h879, hlam]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h853, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p855_1, u2elo1]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  rcases p855_3 (m.d 0 2) (by simp) with h883 | h883
                                  · linarith only [h0, h883, hlam]
                                  · linarith only [h817, h883, hlam]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h815, hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h842, hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h849, hlam, p855_1]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h851, hlam, p855_1]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h816, hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h843, hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h816, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p855_1, u2elo0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h0, h816, h851, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p855_1, u2elo1]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h817, hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h844, hlam, p855_0]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p855_1, u5elo2]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [h853, hlam, p855_1]
                                · have p855_0 := h855c.1
                                  have p855_1 := h855c.2.1
                                  have p855_2 := h855c.2.2.1
                                  have p855_3 := h855c.2.2.2
                                  linarith only [hlam, p855_0]
                              · linarith only [h814, h818, h842, h854, hc23, hlam, hphi, ht34, ht45, u5elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h902 | h902
                              · rcases h2bigk with h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h0, hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  rcases p903_3 (m.d 0 2) (by simp) with h906 | h906
                                  · rcases p903_3 (m.d 1 2) (by simp) with h907 | h907
                                    · rcases p903_3 (m.d 2 3) (by simp) with h908 | h908
                                      · linarith only [h908, hlam, p903_0]
                                      · rcases p903_3 (m.d 2 4) (by simp) with h910 | h910
                                        · linarith only [h816, h910, hlam]
                                        · linarith only [h849, h910, hlam]
                                    · linarith only [h842, h907, hlam]
                                  · linarith only [h906, hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  rcases p903_3 (m.d 0 2) (by simp) with h915 | h915
                                  · rcases p903_3 (m.d 1 2) (by simp) with h916 | h916
                                    · rcases p903_3 (m.d 2 3) (by simp) with h917 | h917
                                      · linarith only [h815, h917, hlam]
                                      · rcases p903_3 (m.d 2 4) (by simp) with h919 | h919
                                        · linarith only [h919, hlam, p903_0]
                                        · rcases p903_3 (m.d 2 5) (by simp) with h921 | h921
                                          · linarith only [h817, h921, hlam]
                                          · linarith only [h853, h921, hlam]
                                    · linarith only [h843, h916, hlam]
                                  · linarith only [h915, hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  rcases p903_3 (m.d 0 2) (by simp) with h926 | h926
                                  · rcases p903_3 (m.d 1 2) (by simp) with h927 | h927
                                    · rcases p903_3 (m.d 2 3) (by simp) with h928 | h928
                                      · linarith only [h815, h928, hlam]
                                      · rcases p903_3 (m.d 2 4) (by simp) with h930 | h930
                                        · linarith only [h816, h930, hlam]
                                        · rcases p903_3 (m.d 2 5) (by simp) with h932 | h932
                                          · linarith only [h932, hlam, p903_0]
                                          · rcases h3bigk with h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [hlam, p934_0]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h830, h842, hc23, hc35, hlam, hphi, p934_1]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h830, hc23, hlam, hphi, ht34, ht45, p934_1, u5elo3]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h818, hlam, p934_0]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h830, hlam, p934_0]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h814, hlam, p934_0]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [hlam, p934_0]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h0, h814, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p934_1, u2elo1]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h845, hlam, p934_0]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h847, hlam, p934_0]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h815, hlam, p934_1]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h842, hlam, p934_1]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [hlam, p934_0]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h849, hlam, p934_0]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h851, hlam, p934_0]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              rcases p934_3 (m.d 0 3) (by simp) with h950 | h950
                                              · linarith only [h950, hlam, p934_0]
                                              · rcases p934_3 (m.d 1 3) (by simp) with h952 | h952
                                                · linarith only [h845, h952, hlam]
                                                · rcases p934_3 (m.d 2 3) (by simp) with h954 | h954
                                                  · linarith only [h849, h954, hlam]
                                                  · rcases p934_3 (m.d 3 4) (by simp) with h956 | h956
                                                    · rcases p934_3 (m.d 3 5) (by simp) with h957 | h957
                                                      · linarith only [h902, h957, hlam]
                                                      · linarith only [h830, h957, hlam]
                                                    · linarith only [h956, hlam, p934_0]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              rcases p934_3 (m.d 0 3) (by simp) with h961 | h961
                                              · linarith only [h818, h961, hlam]
                                              · linarith only [h814, h961, hlam]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              rcases p934_3 (m.d 0 3) (by simp) with h964 | h964
                                              · linarith only [h818, h964, hlam]
                                              · linarith only [h815, h964, hlam]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [hlam, p934_0]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h830, hc03, hc34, hlam, hphi, p934_1]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [hc03, hlam, hphi, ht34, ht45, p934_1, u5elo3]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h842, hc23, hlam, hphi, ht34, ht45, p934_1, u5elo3]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [hc23, hlam, hphi, ht34, ht45, p934_1, u5elo3]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [h902, hlam, p934_1]
                                            · have p934_0 := h934c.1
                                              have p934_1 := h934c.2.1
                                              have p934_2 := h934c.2.2.1
                                              have p934_3 := h934c.2.2.2
                                              linarith only [hlam, p934_0]
                                    · linarith only [h844, h927, hlam]
                                  · linarith only [h926, hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [hc02, hlam, hphi, p903_1, u2elo1]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  rcases p903_3 (m.d 0 2) (by simp) with h978 | h978
                                  · linarith only [h0, h978, hlam]
                                  · linarith only [h815, h978, hlam]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  rcases p903_3 (m.d 0 2) (by simp) with h981 | h981
                                  · linarith only [h0, h981, hlam]
                                  · linarith only [h816, h981, hlam]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  rcases p903_3 (m.d 0 2) (by simp) with h984 | h984
                                  · linarith only [h0, h984, hlam]
                                  · linarith only [h817, h984, hlam]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h815, hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h842, hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h849, hlam, p903_1]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h851, hlam, p903_1]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h816, hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h843, hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h844, h853, hc23, hlam, hphi, ht34, ht45, p903_1, u5elo1]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h853, hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h817, hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h844, hlam, p903_0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h817, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p903_1, u2elo0]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [h0, h817, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p903_1, u2elo1]
                                · have p903_0 := h903c.1
                                  have p903_1 := h903c.2.1
                                  have p903_2 := h903c.2.2.1
                                  have p903_3 := h903c.2.2.2
                                  linarith only [hlam, p903_0]
                              · linarith only [h814, h818, h842, h902, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h817, h844, hlam]
                · linarith only [h0, h814, h842, h843, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h814, h842, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h816, h817, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1007 | h1007
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1008 | h1008
          · linarith only [h0, h1008, h814, h816, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1010 | h1010
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1011 | h1011
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1012 | h1012
                · linarith only [h0, h1011, h1012, h814, h816, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h1011, h1012, h814, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h1011, h814, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1016 | h1016
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1017 | h1017
                · linarith only [h1017, h816, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1016, h1017, h814, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h1016, h814, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h1007, h815, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · linarith only [h0, h814, h815, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1023 | h1023
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1024 | h1024
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1025 | h1025
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1026 | h1026
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1027 | h1027
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1028 | h1028
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1029 | h1029
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1030 | h1030
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1031 | h1031
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1032 | h1032
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1033 | h1033
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1034 | h1034
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1035 | h1035
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1036 | h1036
                              · linarith only [h1023, h1033, h1036, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h0, h1023, h1033, h1035, h1036, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1039 | h1039
                              · linarith only [h0, h1023, h1026, h1035, h1039, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases h2bigk with h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h0, hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h0, h1034, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1041_1, u2elo1]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  rcases p1041_3 (m.d 0 2) (by simp) with h1045 | h1045
                                  · rcases p1041_3 (m.d 1 2) (by simp) with h1046 | h1046
                                    · rcases p1041_3 (m.d 2 3) (by simp) with h1047 | h1047
                                      · linarith only [h1023, h1047, hlam]
                                      · linarith only [h1033, h1047, hlam]
                                    · linarith only [h1029, h1046, hlam]
                                  · linarith only [h1045, hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  rcases p1041_3 (m.d 0 2) (by simp) with h1052 | h1052
                                  · rcases p1041_3 (m.d 1 2) (by simp) with h1053 | h1053
                                    · rcases p1041_3 (m.d 2 3) (by simp) with h1054 | h1054
                                      · linarith only [h1023, h1054, hlam]
                                      · linarith only [h1034, h1054, hlam]
                                    · linarith only [h1030, h1053, hlam]
                                  · linarith only [h1052, hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1041_1, u2elo1]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h1034, h1039, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1041_1, u2elo1]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  rcases p1041_3 (m.d 0 2) (by simp) with h1062 | h1062
                                  · linarith only [h0, h1062, hlam]
                                  · linarith only [h1024, h1062, hlam]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  rcases p1041_3 (m.d 0 2) (by simp) with h1065 | h1065
                                  · linarith only [h0, h1065, hlam]
                                  · linarith only [h1025, h1065, hlam]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h1023, hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h1028, hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h1023, h1033, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1041_1, u2elo0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h0, h1023, h1034, h1039, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1041_1, u2elo1]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h1024, hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h1029, hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h1033, hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h1035, hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h1025, hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h1030, hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h1034, hlam, p1041_0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [h1025, h1033, hc34, hlam, hphi, ht45, p1041_1, u5elo0]
                                · have p1041_0 := h1041c.1
                                  have p1041_1 := h1041c.2.1
                                  have p1041_2 := h1041c.2.2.1
                                  have p1041_3 := h1041c.2.2.2
                                  linarith only [hlam, p1041_0]
                          · linarith only [h1027, h1028, h1033, h1034, h814, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1084 | h1084
                          · linarith only [h1026, h1028, h1033, h1084, h814, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1086 | h1086
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1087 | h1087
                              · rcases h2bigk with h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c | h1088c
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h0, hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  rcases p1088_3 (m.d 0 2) (by simp) with h1091 | h1091
                                  · rcases p1088_3 (m.d 1 2) (by simp) with h1092 | h1092
                                    · rcases p1088_3 (m.d 2 3) (by simp) with h1093 | h1093
                                      · linarith only [h1093, hlam, p1088_0]
                                      · rcases p1088_3 (m.d 2 4) (by simp) with h1095 | h1095
                                        · linarith only [h1024, h1095, hlam]
                                        · linarith only [h1033, h1095, hlam]
                                    · linarith only [h1028, h1092, hlam]
                                  · linarith only [h1091, hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h0, h1086, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1088_1, u2elo1]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  rcases p1088_3 (m.d 0 2) (by simp) with h1101 | h1101
                                  · rcases p1088_3 (m.d 1 2) (by simp) with h1102 | h1102
                                    · rcases p1088_3 (m.d 2 3) (by simp) with h1103 | h1103
                                      · linarith only [h1023, h1103, hlam]
                                      · rcases p1088_3 (m.d 2 4) (by simp) with h1105 | h1105
                                        · linarith only [h1024, h1105, hlam]
                                        · linarith only [h1086, h1105, hlam]
                                    · linarith only [h1030, h1102, hlam]
                                  · linarith only [h1101, hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1088_1, u2elo1]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  rcases p1088_3 (m.d 0 2) (by simp) with h1112 | h1112
                                  · linarith only [h0, h1112, hlam]
                                  · linarith only [h1023, h1112, hlam]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h1086, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1088_1, u2elo1]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  rcases p1088_3 (m.d 0 2) (by simp) with h1116 | h1116
                                  · linarith only [h0, h1116, hlam]
                                  · linarith only [h1025, h1116, hlam]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h1023, hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h1028, hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h1033, hlam, p1088_1]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h1084, hlam, p1088_1]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h1024, hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h1029, hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h1024, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1088_1, u2elo0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h1026, h1028, h1033, h1084, h814, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1088_1, u2elo1]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h1025, hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h1030, hlam, p1088_0]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p1088_1, u5elo2]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [h1086, hlam, p1088_1]
                                · have p1088_0 := h1088c.1
                                  have p1088_1 := h1088c.2.1
                                  have p1088_2 := h1088c.2.2.1
                                  have p1088_3 := h1088c.2.2.2
                                  linarith only [hlam, p1088_0]
                              · linarith only [h1033, h1087, hc23, hlam, hphi, ht34, ht45, u5elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1135 | h1135
                              · linarith only [h1026, h1028, h1086, h1135, h814, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · linarith only [h1033, h1135, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h1027, h1032, h814, hlam]
                    · linarith only [h1026, h1031, h814, hlam]
                  · linarith only [h1026, h1028, h1030, h814, hc34, hlam, hphi, ht45, u5elo2]
                · linarith only [h1028, h1029, h814, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h1028, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h1026, h1027, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1144 | h1144
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1145 | h1145
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1146 | h1146
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1147 | h1147
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1148 | h1148
                    · linarith only [h1026, h1144, h1145, h1148, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1150 | h1150
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1151 | h1151
                        · linarith only [h1023, h1148, h1151, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1153 | h1153
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1154 | h1154
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1155 | h1155
                              · rcases h2bigk with h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h0, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h0, h1153, h1155, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1156_1, u2elo1]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h0, h1151, h1153, h1155, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1156_1, u2elo1]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  rcases p1156_3 (m.d 0 2) (by simp) with h1161 | h1161
                                  · rcases p1156_3 (m.d 1 2) (by simp) with h1162 | h1162
                                    · rcases p1156_3 (m.d 2 3) (by simp) with h1163 | h1163
                                      · linarith only [h1023, h1163, hlam]
                                      · linarith only [h1153, h1163, hlam]
                                    · linarith only [h1147, h1162, hlam]
                                  · linarith only [h1161, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1156_1, u2elo1]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1153, h1155, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1156_1, u2elo1]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1151, h1153, h1155, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1156_1, u2elo1]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  rcases p1156_3 (m.d 0 2) (by simp) with h1172 | h1172
                                  · linarith only [h0, h1172, hlam]
                                  · linarith only [h1025, h1172, hlam]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1023, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1145, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1151, hlam, p1156_1]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1024, h1151, h1153, h1155, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1156_1, u2elo0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1024, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1146, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h0, h1024, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1156_1, u2elo1]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h0, h1024, h1153, h1155, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1156_1, u2elo1]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1025, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1147, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1153, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1154, hlam, p1156_1]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hlam, p1156_0]
                              · linarith only [h1148, h1155, h814, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h1151, h1153, h1154, hc35, hlam, hphi, u5elo4]
                          · linarith only [h1144, h1148, h1153, h814, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1024, h1026, h1144, h1150, h814, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1024, h1026, h1144, h1147, hc35, hlam, hphi, u5elo2]
                · linarith only [h1145, h1146, h814, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h1145, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1197 | h1197
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1198 | h1198
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1199 | h1199
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1200 | h1200
                    · linarith only [h1026, h1197, h1200, h814, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1202 | h1202
                      · linarith only [h1144, h1198, h1200, h1202, h814, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h1202, h814, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h1025, h1199, hlam]
                · linarith only [h0, h1024, h1198, hlam]
              · linarith only [h0, h1023, h1024, h1144, h1197, hc24, hlam, hphi, ht45, u5elo0]
        · linarith only [h1023, h1025, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1209 | h1209
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1210 | h1210
          · linarith only [h1023, h1024, h1210, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1212 | h1212
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1213 | h1213
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1214 | h1214
                · linarith only [h1023, h1024, h1214, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h1214, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h1213, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1218 | h1218
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1219 | h1219
                · linarith only [h1024, h1219, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1219, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h1218, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h1023, h1209, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1224 | h1224
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1225 | h1225
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1226 | h1226
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1227 | h1227
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1228 | h1228
              · linarith only [h1023, h1224, h1228, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h0, h1228, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h1023, h1224, h1227, hc24, hlam, hphi, ht45, u5elo3]
          · linarith only [h1023, h1224, h1226, hlam]
        · linarith only [h1224, h1225, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1234 | h1234
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1235 | h1235
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1236 | h1236
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1237 | h1237
              · linarith only [h1023, h1237, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h1237, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h1224, h1234, h1235, h1236, hc25, hlam, hphi, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1241 | h1241
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1242 | h1242
              · linarith only [h1023, h1234, h1242, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h0, h1242, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h1023, h1234, h1241, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1246 | h1246
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1247 | h1247
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1248 | h1248
              · linarith only [h1023, h1248, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h1248, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h1246, h1247, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1252 | h1252
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1253 | h1253
              · linarith only [h0, h1023, h1253, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h1253, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1256 | h1256
              · linarith only [h0, h1023, h1256, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h1256, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_22_13_15_M_LI_L_I_L_0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_13_15_M_LI_L_I_L_0_x0 m hb2 hb3 hb5 h0
  · exact r1l7_22_13_15_M_LI_L_I_L_0_x1 m hb2 hb3 hb5 h0

end R2N4
