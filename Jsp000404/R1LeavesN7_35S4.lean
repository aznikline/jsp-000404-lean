import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_35S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6604000 in
set_option maxHeartbeats 6604000 in
theorem r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h811 | h811
  · rcases m.htr 0 1 4 (by decide) (by decide) with h812 | h812
    · rcases m.htr 0 1 5 (by decide) (by decide) with h813 | h813
      · rcases m.htr 0 2 3 (by decide) (by decide) with h814 | h814
        · rcases m.htr 0 2 4 (by decide) (by decide) with h815 | h815
          · rcases m.htr 0 3 4 (by decide) (by decide) with h816 | h816
            · rcases m.htr 0 3 5 (by decide) (by decide) with h817 | h817
              · rcases m.htr 0 4 5 (by decide) (by decide) with h818 | h818
                · rcases m.htr 1 2 3 (by decide) (by decide) with h819 | h819
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h820 | h820
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h821 | h821
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h822 | h822
                        · linarith only [h811, h822, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h811, h816, h822, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h813, h821, hlam]
                    · linarith only [h0, h815, h820, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h811, h814, h816, h819, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h828 | h828
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h829 | h829
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h830 | h830
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h831 | h831
                        · linarith only [h811, h831, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h816, h831, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h813, h830, hlam]
                    · linarith only [h0, h815, h829, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h811, h814, h828, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h837 | h837
                · linarith only [h816, h817, h837, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h839 | h839
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h840 | h840
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h841 | h841
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h842 | h842
                        · linarith only [h811, h842, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h811, h816, h839, h842, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h813, h841, hlam]
                    · linarith only [h0, h815, h840, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h813, h814, h816, h817, h839, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h848 | h848
              · rcases m.htr 0 4 5 (by decide) (by decide) with h849 | h849
                · rcases m.htr 1 2 3 (by decide) (by decide) with h850 | h850
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h851 | h851
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h852 | h852
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h853 | h853
                        · linarith only [h811, h816, h848, h853, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h855 | h855
                          · linarith only [h0, h812, h853, h855, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h848, h855, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h813, h852, hlam]
                    · linarith only [h0, h815, h851, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h811, h814, h850, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h816, h848, h849, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h862 | h862
                · rcases m.htr 1 2 3 (by decide) (by decide) with h863 | h863
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h864 | h864
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h865 | h865
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h866 | h866
                        · linarith only [h811, h816, h866, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h868 | h868
                          · linarith only [h811, h848, h868, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h870 | h870
                            · linarith only [h0, h812, h870, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h862, h870, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h813, h865, hlam]
                    · linarith only [h0, h815, h864, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h811, h814, h863, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h876 | h876
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h877 | h877
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h878 | h878
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h879 | h879
                        · linarith only [h811, h816, h879, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h881 | h881
                          · linarith only [h0, h811, h848, h862, h881, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h883 | h883
                            · linarith only [h812, h862, h883, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h885 | h885
                              · linarith only [h812, h816, h876, h879, h885, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h887 | h887
                                · linarith only [h0, h811, h848, h862, h876, h887, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h889 | h889
                                  · linarith only [h815, h816, h862, h889, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h891 | h891
                                    · rcases h1bigk with h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [hlam, p892_0]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h0, hlam, p892_0]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h876, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p892_1, u0elo0]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h0, h876, h879, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p892_1, u0elo1]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h0, h876, h879, h883, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p892_1, u0elo1]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        rcases p892_3 (m.d 0 1) (by simp) with h898 | h898
                                        · linarith only [h898, hlam, p892_0]
                                        · rcases p892_3 (m.d 1 2) (by simp) with h900 | h900
                                          · rcases p892_3 (m.d 1 3) (by simp) with h901 | h901
                                            · linarith only [h876, h901, hlam]
                                            · rcases p892_3 (m.d 1 4) (by simp) with h903 | h903
                                              · linarith only [h877, h903, hlam]
                                              · rcases p892_3 (m.d 1 5) (by simp) with h905 | h905
                                                · linarith only [h878, h905, hlam]
                                                · rcases h3bigk with h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h876, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p907_1, u0elo2]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h816, h862, h891, hc23, hc34, hlam, hphi, p907_1]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h816, hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h848, hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h811, hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h0, h811, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p907_1, u0elo1]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h879, hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h881, hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h814, hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h876, hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h885, hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h887, hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    rcases p907_3 (m.d 0 3) (by simp) with h923 | h923
                                                    · linarith only [h923, hlam, p907_0]
                                                    · rcases p907_3 (m.d 1 3) (by simp) with h925 | h925
                                                      · linarith only [h879, h925, hlam]
                                                      · rcases p907_3 (m.d 2 3) (by simp) with h927 | h927
                                                        · linarith only [h885, h927, hlam]
                                                        · rcases p907_3 (m.d 3 4) (by simp) with h929 | h929
                                                          · rcases p907_3 (m.d 3 5) (by simp) with h930 | h930
                                                            · linarith only [h891, h930, hlam]
                                                            · linarith only [h848, h930, hlam]
                                                          · linarith only [h929, hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    rcases p907_3 (m.d 0 3) (by simp) with h934 | h934
                                                    · linarith only [h816, h934, hlam]
                                                    · linarith only [h811, h934, hlam]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    rcases p907_3 (m.d 0 3) (by simp) with h937 | h937
                                                    · linarith only [h816, h937, hlam]
                                                    · linarith only [h814, h937, hlam]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h816, h862, h891, hc03, hc34, hlam, hphi, p907_1]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    rcases p907_3 (m.d 0 3) (by simp) with h942 | h942
                                                    · linarith only [h942, hlam, p907_0]
                                                    · rcases p907_3 (m.d 1 3) (by simp) with h944 | h944
                                                      · linarith only [h881, h944, hlam]
                                                      · rcases p907_3 (m.d 2 3) (by simp) with h946 | h946
                                                        · linarith only [h887, h946, hlam]
                                                        · rcases p907_3 (m.d 3 4) (by simp) with h948 | h948
                                                          · rcases p907_3 (m.d 3 5) (by simp) with h949 | h949
                                                            · rcases h4bigk with h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c | h950c
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [hlam, p950_0]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p950_1, u0elo3]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h0, h812, hc24, hlam, hphi, ht0b, ht45, ht5b, p950_1, u0elo1]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h816, hlam, p950_0]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h862, hlam, p950_0]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h812, hlam, p950_1]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [hlam, p950_0]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h0, h812, hc24, hlam, hphi, ht0b, ht45, ht5b, p950_1, u0elo1]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h879, hlam, p950_1]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h883, hlam, p950_0]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h815, hlam, p950_1]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h877, hlam, p950_1]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [hlam, p950_0]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h885, hlam, p950_1]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h889, hlam, p950_0]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                rcases p950_3 (m.d 0 4) (by simp) with h966 | h966
                                                                · linarith only [h816, h966, hlam]
                                                                · rcases p950_3 (m.d 1 4) (by simp) with h968 | h968
                                                                  · linarith only [h879, h968, hlam]
                                                                  · rcases p950_3 (m.d 2 4) (by simp) with h970 | h970
                                                                    · linarith only [h885, h970, hlam]
                                                                    · rcases p950_3 (m.d 3 4) (by simp) with h972 | h972
                                                                      · rcases p950_3 (m.d 4 5) (by simp) with h973 | h973
                                                                        · linarith only [h891, h973, hlam]
                                                                        · linarith only [h862, h973, hlam]
                                                                      · linarith only [h816, h972, hlam]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                rcases p950_3 (m.d 0 4) (by simp) with h977 | h977
                                                                · linarith only [h816, h977, hlam]
                                                                · linarith only [h812, h977, hlam]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                rcases p950_3 (m.d 0 4) (by simp) with h980 | h980
                                                                · linarith only [h816, h980, hlam]
                                                                · linarith only [h815, h980, hlam]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [hlam, p950_0]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h815, h862, h885, hc23, hc34, hlam, hphi, p950_1]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h811, h816, h876, h891, hc23, hc34, hlam, hphi, p950_1]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h877, h885, h891, hc23, hc34, hlam, hphi, p950_1]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h885, h891, hc23, hc34, hlam, hphi, p950_1]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [h891, hlam, p950_0]
                                                              · have p950_0 := h950c.1
                                                                have p950_1 := h950c.2.1
                                                                have p950_2 := h950c.2.2.1
                                                                have p950_3 := h950c.2.2.2
                                                                linarith only [hlam, p950_0]
                                                            · linarith only [h949, hlam, p907_0]
                                                          · linarith only [h816, h948, hlam]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    rcases p907_3 (m.d 0 3) (by simp) with h992 | h992
                                                    · linarith only [h848, h992, hlam]
                                                    · linarith only [h811, h992, hlam]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    rcases p907_3 (m.d 0 3) (by simp) with h995 | h995
                                                    · linarith only [h848, h995, hlam]
                                                    · linarith only [h814, h995, hlam]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [h891, hlam, p907_0]
                                                  · have p907_0 := h907c.1
                                                    have p907_1 := h907c.2.1
                                                    have p907_2 := h907c.2.2.1
                                                    have p907_3 := h907c.2.2.2
                                                    linarith only [hlam, p907_0]
                                          · linarith only [h900, hlam, p892_0]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [hlam, p892_0]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        rcases p892_3 (m.d 0 1) (by simp) with h1002 | h1002
                                        · linarith only [h0, h1002, hlam]
                                        · linarith only [h1002, h811, hlam]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        rcases p892_3 (m.d 0 1) (by simp) with h1005 | h1005
                                        · linarith only [h0, h1005, hlam]
                                        · linarith only [h1005, h812, hlam]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        rcases p892_3 (m.d 0 1) (by simp) with h1008 | h1008
                                        · linarith only [h0, h1008, hlam]
                                        · linarith only [h1008, h813, hlam]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h811, hlam, p892_0]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h876, hlam, p892_1]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [hlam, p892_0]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h879, hlam, p892_1]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h881, hlam, p892_1]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h812, hlam, p892_0]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h877, hlam, p892_1]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h0, h812, h876, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p892_1, u0elo1]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [hlam, p892_0]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h883, hlam, p892_1]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h813, hlam, p892_0]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h878, hlam, p892_1]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h0, h813, h876, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p892_1, u0elo1]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [h0, h813, hc14, hlam, hphi, ht0b, ht45, ht5b, p892_1, u0elo1]
                                      · have p892_0 := h892c.1
                                        have p892_1 := h892c.2.1
                                        have p892_2 := h892c.2.2.1
                                        have p892_3 := h892c.2.2.2
                                        linarith only [hlam, p892_0]
                                    · rcases h1bigk with h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [hlam, p1026_0]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h0, hlam, p1026_0]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h0, h876, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1026_1, u0elo1]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h0, h877, h885, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1026_1, u0elo1]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h0, hc15, hlam, hphi, ht0b, ht5b, p1026_1, u0elo1]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        rcases p1026_3 (m.d 0 1) (by simp) with h1032 | h1032
                                        · linarith only [h1032, hlam, p1026_0]
                                        · rcases p1026_3 (m.d 1 2) (by simp) with h1034 | h1034
                                          · rcases p1026_3 (m.d 1 3) (by simp) with h1035 | h1035
                                            · linarith only [h1035, h876, hlam]
                                            · rcases p1026_3 (m.d 1 4) (by simp) with h1037 | h1037
                                              · linarith only [h1037, h877, hlam]
                                              · rcases p1026_3 (m.d 1 5) (by simp) with h1039 | h1039
                                                · linarith only [h1039, h878, hlam]
                                                · rcases h3bigk with h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h876, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1041_1, u0elo2]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h0, h811, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1041_1, u0elo1]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h816, hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h848, hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h811, hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h0, h811, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1041_1, u0elo1]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h879, hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h881, hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h814, hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h876, hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h885, hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h887, hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h891, hc03, hc45, hlam, hphi, ht34, p1041_1]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h876, h891, hc23, hc45, hlam, hphi, ht34, p1041_1]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h891, hc23, hc45, hlam, hphi, ht34, p1041_1]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [hlam, p1041_0]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h891, hlam, p1041_1]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    rcases p1041_3 (m.d 0 3) (by simp) with h1062 | h1062
                                                    · linarith only [h1062, hlam, p1041_0]
                                                    · rcases p1041_3 (m.d 1 3) (by simp) with h1064 | h1064
                                                      · linarith only [h1064, h881, hlam]
                                                      · rcases p1041_3 (m.d 2 3) (by simp) with h1066 | h1066
                                                        · linarith only [h1066, h887, hlam]
                                                        · rcases p1041_3 (m.d 3 4) (by simp) with h1068 | h1068
                                                          · linarith only [h1068, h891, hlam]
                                                          · linarith only [h1068, h816, hlam]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    rcases p1041_3 (m.d 0 3) (by simp) with h1071 | h1071
                                                    · linarith only [h1071, h848, hlam]
                                                    · linarith only [h1071, h811, hlam]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    rcases p1041_3 (m.d 0 3) (by simp) with h1074 | h1074
                                                    · linarith only [h1074, h848, hlam]
                                                    · linarith only [h1074, h814, hlam]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [h811, h816, h876, h891, hc23, hc45, hlam, hphi, ht34, p1041_1]
                                                  · have p1041_0 := h1041c.1
                                                    have p1041_1 := h1041c.2.1
                                                    have p1041_2 := h1041c.2.2.1
                                                    have p1041_3 := h1041c.2.2.2
                                                    linarith only [hlam, p1041_0]
                                          · linarith only [h1034, hlam, p1026_0]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [hlam, p1026_0]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        rcases p1026_3 (m.d 0 1) (by simp) with h1081 | h1081
                                        · linarith only [h0, h1081, hlam]
                                        · linarith only [h1081, h811, hlam]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        rcases p1026_3 (m.d 0 1) (by simp) with h1084 | h1084
                                        · linarith only [h0, h1084, hlam]
                                        · linarith only [h1084, h812, hlam]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        rcases p1026_3 (m.d 0 1) (by simp) with h1087 | h1087
                                        · linarith only [h0, h1087, hlam]
                                        · linarith only [h1087, h813, hlam]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h811, hlam, p1026_0]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h876, hlam, p1026_1]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [hlam, p1026_0]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h879, hlam, p1026_1]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h881, hlam, p1026_1]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h812, hlam, p1026_0]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h877, hlam, p1026_1]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h0, h812, h876, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1026_1, u0elo1]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [hlam, p1026_0]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h883, hlam, p1026_1]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h813, hlam, p1026_0]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h878, hlam, p1026_1]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h0, h813, h876, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1026_1, u0elo1]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [h0, h813, hc14, hlam, hphi, ht0b, ht45, ht5b, p1026_1, u0elo1]
                                      · have p1026_0 := h1026c.1
                                        have p1026_1 := h1026c.2.1
                                        have p1026_2 := h1026c.2.2.1
                                        have p1026_3 := h1026c.2.2.2
                                        linarith only [hlam, p1026_0]
                      · linarith only [h0, h813, h878, hlam]
                    · linarith only [h0, h811, h815, h876, h877, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h814, h876, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h812, h815, hlam]
        · linarith only [h0, h811, h814, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1110 | h1110
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1111 | h1111
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1112 | h1112
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1113 | h1113
              · linarith only [h1113, h811, h813, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1115 | h1115
                · linarith only [h1112, h1115, h811, h813, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1117 | h1117
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1118 | h1118
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1119 | h1119
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1120 | h1120
                        · linarith only [h1120, h811, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h1112, h1120, h811, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1123 | h1123
                        · linarith only [h0, h1119, h1123, h811, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1112, h1119, h1123, h811, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h1111, h1118, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1110, h1117, h811, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1128 | h1128
              · linarith only [h1112, h1128, h812, h813, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1130 | h1130
                · linarith only [h1130, h812, h813, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1132 | h1132
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1133 | h1133
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1134 | h1134
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1135 | h1135
                        · linarith only [h1112, h1135, h811, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1137 | h1137
                          · linarith only [h1128, h1137, h811, h813, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1139 | h1139
                            · linarith only [h0, h1112, h1130, h1139, h812, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1141 | h1141
                              · linarith only [h1112, h1132, h1141, h811, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1143 | h1143
                                · linarith only [h1132, h1137, h1143, h811, h813, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1145 | h1145
                                  · linarith only [h1133, h1139, h1145, h812, h813, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1147 | h1147
                                    · linarith only [h1133, h1139, h1141, h1147, h812, h813, hc23, hc34, hlam, hphi]
                                    · rcases h1bigk with h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [hlam, p1149_0]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h0, hlam, p1149_0]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1149_1, u0elo0]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h0, hc14, hlam, hphi, ht0b, ht45, ht5b, p1149_1, u0elo1]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h813, hlam, p1149_0]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        rcases p1149_3 (m.d 0 1) (by simp) with h1155 | h1155
                                        · linarith only [h1155, hlam, p1149_0]
                                        · rcases p1149_3 (m.d 1 2) (by simp) with h1157 | h1157
                                          · rcases p1149_3 (m.d 1 3) (by simp) with h1158 | h1158
                                            · linarith only [h1132, h1158, hlam]
                                            · rcases p1149_3 (m.d 1 4) (by simp) with h1160 | h1160
                                              · linarith only [h1133, h1160, hlam]
                                              · rcases p1149_3 (m.d 1 5) (by simp) with h1162 | h1162
                                                · linarith only [h1134, h1162, hlam]
                                                · linarith only [h1162, h813, hlam]
                                          · linarith only [h1157, hlam, p1149_0]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [hlam, p1149_0]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        rcases p1149_3 (m.d 0 1) (by simp) with h1167 | h1167
                                        · linarith only [h0, h1167, hlam]
                                        · linarith only [h1167, h811, hlam]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        rcases p1149_3 (m.d 0 1) (by simp) with h1170 | h1170
                                        · linarith only [h0, h1170, hlam]
                                        · linarith only [h1170, h812, hlam]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h813, hc01, hc12, hlam, hphi, p1149_1]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h811, hlam, p1149_0]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h1132, hlam, p1149_1]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [hlam, p1149_0]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h1135, hlam, p1149_1]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h1137, hlam, p1149_1]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h812, hlam, p1149_0]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h1133, hlam, p1149_1]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h1132, h812, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1149_1, u0elo0]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [hlam, p1149_0]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h1139, hlam, p1149_1]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h1132, h1137, h811, hc23, hc35, hlam, hphi, p1149_1]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [h1134, hlam, p1149_1]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        rcases p1149_3 (m.d 0 1) (by simp) with h1186 | h1186
                                        · linarith only [h1186, h813, hlam]
                                        · linarith only [h1186, h811, hlam]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        rcases p1149_3 (m.d 0 1) (by simp) with h1189 | h1189
                                        · linarith only [h1189, h813, hlam]
                                        · linarith only [h1189, h812, hlam]
                                      · have p1149_0 := h1149c.1
                                        have p1149_1 := h1149c.2.1
                                        have p1149_2 := h1149c.2.2.1
                                        have p1149_3 := h1149c.2.2.2
                                        linarith only [hlam, p1149_0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1193 | h1193
                        · linarith only [h0, h1112, h1134, h1193, h811, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1195 | h1195
                          · linarith only [h0, h1134, h1195, h811, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1197 | h1197
                            · linarith only [h0, h1134, h1197, h812, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1199 | h1199
                              · linarith only [h1110, h1112, h1199, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1201 | h1201
                                · linarith only [h0, h1132, h1134, h1195, h1201, h811, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h1132, h1134, h1201, h811, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h1111, h1132, h1133, h811, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1110, h1132, h811, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h1111, h812, hlam]
        · linarith only [h0, h1110, h811, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1208 | h1208
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1209 | h1209
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1210 | h1210
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1211 | h1211
            · linarith only [h1211, h811, h812, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1213 | h1213
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1214 | h1214
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1215 | h1215
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1216 | h1216
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1217 | h1217
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1218 | h1218
                        · linarith only [h1211, h1218, h811, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1220 | h1220
                          · linarith only [h1210, h1220, h811, h812, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h1213, h1220, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1208, h1216, h1217, h812, hlam]
                    · linarith only [h1210, h1216, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1209, h1215, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1213, h1214, h811, h812, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1227 | h1227
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1228 | h1228
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1229 | h1229
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1230 | h1230
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1231 | h1231
                        · linarith only [h1231, h811, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1233 | h1233
                          · linarith only [h1210, h1213, h1233, h811, h812, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1235 | h1235
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1236 | h1236
                              · linarith only [h1228, h1231, h1236, h811, h812, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1238 | h1238
                                · linarith only [h1208, h1213, h1228, h1233, h1238, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1240 | h1240
                                  · linarith only [h1210, h1240, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h1210, h1227, h1240, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h1210, h1227, h1235, h812, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1208, h1229, h1230, h812, hlam]
                    · linarith only [h1210, h1229, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1209, h1228, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1208, h1227, h812, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1248 | h1248
            · linarith only [h0, h1210, h1248, h811, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1250 | h1250
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1251 | h1251
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1252 | h1252
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1253 | h1253
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1254 | h1254
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1255 | h1255
                        · linarith only [h0, h1210, h1248, h1255, h811, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1257 | h1257
                          · linarith only [h0, h1210, h1257, h811, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h1250, h1257, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1210, h1253, h1254, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1261 | h1261
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1262 | h1262
                        · linarith only [h1248, h1250, h1262, h811, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1264 | h1264
                          · linarith only [h0, h1210, h1264, h811, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h1250, h1264, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1208, h1261, hlam]
                  · linarith only [h0, h1209, h1210, h1252, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h1210, h1250, h1251, h811, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1270 | h1270
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1271 | h1271
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1272 | h1272
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1273 | h1273
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1274 | h1274
                        · linarith only [h0, h1210, h1248, h1274, h811, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1276 | h1276
                          · linarith only [h0, h1210, h1250, h1276, h811, hc05, hlam, hphi, ht0b, ht5b, u0elo3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1278 | h1278
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1279 | h1279
                              · linarith only [h1209, h1210, h1272, h1274, h1279, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1281 | h1281
                                · linarith only [h1250, h1271, h1281, h811, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1283 | h1283
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1284 | h1284
                                    · rcases h1bigk with h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [hlam, p1285_0]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h0, hlam, p1285_0]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h0, h1210, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1285_1, u0elo3]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h812, hlam, p1285_0]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h0, h1210, h1271, h1276, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1285_1, u0elo3]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        rcases p1285_3 (m.d 0 1) (by simp) with h1291 | h1291
                                        · linarith only [h1291, hlam, p1285_0]
                                        · rcases p1285_3 (m.d 1 2) (by simp) with h1293 | h1293
                                          · rcases p1285_3 (m.d 1 3) (by simp) with h1294 | h1294
                                            · linarith only [h1271, h1294, hlam]
                                            · rcases p1285_3 (m.d 1 4) (by simp) with h1296 | h1296
                                              · linarith only [h1272, h1296, hlam]
                                              · linarith only [h1296, h812, hlam]
                                          · linarith only [h1293, hlam, p1285_0]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [hlam, p1285_0]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h0, h1210, h1272, h811, hlam, p1285_2]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h0, h1208, h1210, h1271, h1272, h1276, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1285_1]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h0, h1208, h1210, h1272, hlam, p1285_2]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h811, hlam, p1285_0]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h1271, hlam, p1285_1]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [hlam, p1285_0]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h1274, hlam, p1285_1]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h1276, hlam, p1285_1]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h1208, h1271, h1274, h1276, hc23, hc34, hlam, hphi, p1285_1]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h1272, hlam, p1285_1]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        rcases p1285_3 (m.d 0 1) (by simp) with h1311 | h1311
                                        · linarith only [h1311, h812, hlam]
                                        · linarith only [h1311, h811, hlam]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [hlam, p1285_0]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        rcases p1285_3 (m.d 0 1) (by simp) with h1315 | h1315
                                        · linarith only [h1315, h812, hlam]
                                        · linarith only [h1208, h1315, hlam]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h1208, hlam, p1285_0]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h1273, hlam, p1285_1]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h1208, h1271, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1285_1, u0elo0]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [h1278, hlam, p1285_0]
                                      · have p1285_0 := h1285c.1
                                        have p1285_1 := h1285c.2.1
                                        have p1285_2 := h1285c.2.2.1
                                        have p1285_3 := h1285c.2.2.2
                                        linarith only [hlam, p1285_0]
                                    · linarith only [h0, h1208, h1210, h1273, h1274, h1283, h1284, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                  · linarith only [h0, h1210, h1271, h1283, h811, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h0, h1210, h1270, h1272, h1278, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h0, h1210, h1271, h1272, h1273, h811, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1327 | h1327
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1328 | h1328
                        · linarith only [h1328, h811, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1330 | h1330
                          · linarith only [h1250, h1330, h811, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1332 | h1332
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1333 | h1333
                              · linarith only [h1208, h1271, h1272, h1328, h1330, h1333, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h0, h1208, h1272, h1330, h1333, hc13, hc34, hlam, hphi]
                            · linarith only [h0, h1208, h1271, h1272, h1330, h1332, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1208, h1327, hlam]
                  · linarith only [h0, h1209, h1210, h1271, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h1208, h1210, h1270, hlam]
        · linarith only [h0, h1209, h811, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1341 | h1341
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1342 | h1342
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1343 | h1343
            · linarith only [h1343, h811, h812, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1345 | h1345
              · linarith only [h1208, h1345, h811, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1347 | h1347
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1348 | h1348
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1349 | h1349
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1350 | h1350
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1351 | h1351
                        · linarith only [h1208, h1342, h1343, h1347, h1351, h811, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1353 | h1353
                          · linarith only [h1208, h1345, h1353, h811, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1355 | h1355
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1356 | h1356
                              · linarith only [h1208, h1348, h1351, h1355, h1356, h811, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1358 | h1358
                                · linarith only [h1208, h1348, h1353, h1358, h811, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1360 | h1360
                                  · linarith only [h1342, h1360, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h1347, h1360, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                            · linarith only [h1342, h1347, h1355, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1364 | h1364
                        · linarith only [h1343, h1349, h1350, h1364, h811, h812, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1366 | h1366
                          · linarith only [h1208, h1345, h1366, h811, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1368 | h1368
                            · linarith only [h1349, h1350, h1368, hlam]
                            · linarith only [h1342, h1347, h1368, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1342, h1348, h1349, h811, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1341, h1348, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1373 | h1373
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1374 | h1374
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1375 | h1375
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1376 | h1376
                        · linarith only [h1343, h1376, h811, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1378 | h1378
                          · linarith only [h1345, h1347, h1378, h811, h812, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1380 | h1380
                            · linarith only [h1347, h1373, h1376, h1380, h811, h812, hc23, hc34, hlam, hphi]
                            · linarith only [h1373, h1380, h811, h812, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1383 | h1383
                        · linarith only [h1374, h1375, h1383, h811, h812, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1385 | h1385
                          · linarith only [h1374, h1375, h1385, h811, h812, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1387 | h1387
                            · linarith only [h1347, h1373, h1374, h1375, h1387, h811, h812, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · linarith only [h1373, h1387, h811, h812, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h1342, h1374, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1341, h1373, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1392 | h1392
            · linarith only [h0, h1342, h1392, h811, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1394 | h1394
              · linarith only [h1208, h1394, h811, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1396 | h1396
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1397 | h1397
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1398 | h1398
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1399 | h1399
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1400 | h1400
                        · linarith only [h0, h1342, h1392, h1400, h811, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1402 | h1402
                          · linarith only [h1208, h1394, h1402, h811, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1404 | h1404
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1405 | h1405
                              · linarith only [h1342, h1397, h1398, h1400, h1405, h811, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1407 | h1407
                                · linarith only [h1397, h1402, h1407, h811, hc15, hlam, hphi, ht0b, ht5b, u0elo0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1409 | h1409
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1410 | h1410
                                    · rcases h1bigk with h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [hlam, p1411_0]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h0, hlam, p1411_0]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h1397, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1411_1, u0elo0]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h812, hlam, p1411_0]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h1208, hlam, p1411_0]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        rcases p1411_3 (m.d 0 1) (by simp) with h1417 | h1417
                                        · linarith only [h1417, hlam, p1411_0]
                                        · rcases p1411_3 (m.d 1 2) (by simp) with h1419 | h1419
                                          · rcases p1411_3 (m.d 1 3) (by simp) with h1420 | h1420
                                            · linarith only [h1397, h1420, hlam]
                                            · rcases p1411_3 (m.d 1 4) (by simp) with h1422 | h1422
                                              · linarith only [h1398, h1422, hlam]
                                              · linarith only [h1422, h812, hlam]
                                          · linarith only [h1419, hlam, p1411_0]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [hlam, p1411_0]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h0, h1342, h1398, h811, hlam, p1411_2]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h0, h1342, h1398, hc01, hc12, hlam, hphi, p1411_1]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h1208, h1397, h811, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1411_1]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h811, hlam, p1411_0]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h1397, hlam, p1411_1]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [hlam, p1411_0]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h1400, hlam, p1411_1]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h1402, hlam, p1411_1]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h1397, h1400, h811, hc23, hc34, hlam, hphi, p1411_1]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h1398, hlam, p1411_1]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        rcases p1411_3 (m.d 0 1) (by simp) with h1437 | h1437
                                        · linarith only [h1437, h812, hlam]
                                        · linarith only [h1437, h811, hlam]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [hlam, p1411_0]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h1208, h1397, h1400, h811, hc23, hc34, hlam, hphi, p1411_1]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h1397, h1402, h811, hc23, hc35, hlam, hphi, p1411_1]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h1399, hlam, p1411_1]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        rcases p1411_3 (m.d 0 1) (by simp) with h1444 | h1444
                                        · linarith only [h1208, h1444, hlam]
                                        · linarith only [h1444, h811, hlam]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [h1404, hlam, p1411_0]
                                      · have p1411_0 := h1411c.1
                                        have p1411_1 := h1411c.2.1
                                        have p1411_2 := h1411c.2.2.1
                                        have p1411_3 := h1411c.2.2.2
                                        linarith only [hlam, p1411_0]
                                    · linarith only [h1396, h1400, h1410, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                  · linarith only [h0, h1342, h1396, h1397, h1409, h811, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h0, h1342, h1396, h1397, h1398, h1404, h811, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1342, h1397, h1398, h1399, h811, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1453 | h1453
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1454 | h1454
                        · linarith only [h1454, h811, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1456 | h1456
                          · linarith only [h1208, h1398, h1453, h1456, h811, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1458 | h1458
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1459 | h1459
                              · linarith only [h1208, h1397, h1398, h1453, h1454, h1459, h811, hlam]
                              · linarith only [h1208, h1397, h1398, h1453, h1459, h811, hc23, hc34, hlam, hphi]
                            · linarith only [h1208, h1396, h1397, h1398, h1453, h1458, h811, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1463 | h1463
                        · linarith only [h1463, h811, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1465 | h1465
                          · linarith only [h0, h1398, h1465, h811, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1467 | h1467
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1468 | h1468
                              · linarith only [h0, h1397, h1453, h1463, h1467, h1468, h811, hlam]
                              · linarith only [h0, h1398, h1468, h811, hc13, hc34, hlam, hphi]
                            · linarith only [h0, h1396, h1397, h1398, h1467, h811, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1341, h1397, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1473 | h1473
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1474 | h1474
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1475 | h1475
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1476 | h1476
                        · linarith only [h1476, h811, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1478 | h1478
                          · linarith only [h0, h1342, h1396, h1478, h811, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1480 | h1480
                            · linarith only [h0, h1342, h1396, h1476, h1480, h811, hc13, hc34, hlam, hphi]
                            · linarith only [h1473, h1480, h811, h812, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1342, h1473, h1474, h1475, h811, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1484 | h1484
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1485 | h1485
                        · linarith only [h1485, h811, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1487 | h1487
                          · linarith only [h0, h1342, h1396, h1487, h811, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1489 | h1489
                            · linarith only [h0, h1342, h1396, h1473, h1485, h1489, h811, hc23, hc34, hlam, hphi]
                            · linarith only [h1473, h1489, h811, h812, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1492 | h1492
                        · linarith only [h0, h1342, h1396, h1492, h811, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1494 | h1494
                          · linarith only [h0, h1342, h1396, h1494, h811, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1496 | h1496
                            · linarith only [h0, h1342, h1396, h1473, h1492, h1496, h811, hc23, hc34, hlam, hphi]
                            · linarith only [h1473, h1496, h811, h812, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h1341, h1342, h1396, h1473, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
        · linarith only [h0, h1341, h811, hlam]
  · exact r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1 m hb0 hb1 hb3 hb4 h0 h811

end R2N4
