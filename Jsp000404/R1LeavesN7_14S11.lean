import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_14S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8057 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8058 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 3 4 (by decide) (by decide) with h9836 | h9836
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9837 | h9837
    · linarith only [h8056, h8058, h9837, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9839 | h9839
      · linarith only [h8057, h8058, h9839, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9841 | h9841
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9842 | h9842
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9843 | h9843
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9844 | h9844
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9845 | h9845
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9846 | h9846
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9847 | h9847
                    · linarith only [h8056, h8058, h9843, h9847, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h8056, h8058, h9836, h9843, h9847, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9850 | h9850
                    · linarith only [h8056, h8058, h9843, h9850, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h8056, h8058, h9836, h9843, h9850, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9853 | h9853
                  · linarith only [h6681, h9839, h9844, h9845, h9853, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9855 | h9855
                    · linarith only [h8056, h8058, h9843, h9855, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h8056, h8058, h9836, h9843, h9855, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h4610, h8056, h8058, h9836, h9843, h9844, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9859 | h9859
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9860 | h9860
                · linarith only [h9836, h9837, h9841, h9843, h9860, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9862 | h9862
                  · linarith only [h6681, h9839, h9842, h9843, h9862, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9864 | h9864
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9865 | h9865
                      · linarith only [h8056, h9860, h9865, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9867 | h9867
                        · linarith only [h6681, h9862, h9867, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h8056, h9843, h9864, h9867, hc34, hc45, hlam, hphi]
                    · linarith only [h9836, h9837, h9864, hc23, hc35, hlam, hphi]
              · linarith only [h4610, h9836, h9859, hlam]
          · linarith only [h0, h8057, h9842, hlam]
        · linarith only [h0, h8056, h9841, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9874 | h9874
    · linarith only [h8057, h8058, h9836, h9874, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9876 | h9876
      · linarith only [h8057, h8058, h9876, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9878 | h9878
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9879 | h9879
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9880 | h9880
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9881 | h9881
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9882 | h9882
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9883 | h9883
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9884 | h9884
                    · linarith only [h8056, h8058, h9836, h9880, h9884, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9886 | h9886
                      · linarith only [h4610, h8057, h8058, h9874, h9880, h9884, h9886, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9888 | h9888
                        · linarith only [h8057, h8058, h9878, h9882, h9886, h9888, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9890 | h9890
                          · linarith only [h8057, h8058, h9884, h9888, h9890, hc23, hc34, hlam, hphi]
                          · linarith only [h4610, h9836, h9878, h9881, h9883, h9890, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9893 | h9893
                    · linarith only [h4610, h8056, h8058, h9836, h9893, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9895 | h9895
                      · linarith only [h8057, h8058, h9874, h9880, h9893, h9895, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9897 | h9897
                        · linarith only [h8057, h8058, h9878, h9882, h9883, h9895, h9897, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9899 | h9899
                          · linarith only [h9881, h9883, h9899, hlam]
                          · rcases h0bigk with h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c | h9901c
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [hlam, p9901_0]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h0, hlam, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h4610, hlam, p9901_0]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h6681, hlam, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h7494, hlam, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h8058, h9878, h9882, h9895, hc01, hc12, hlam, hphi, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [hlam, p9901_0]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h4610, h8058, h9878, h9882, h9895, hc01, hc12, hlam, hphi, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h8058, h9878, h9882, h9895, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h8058, hlam, p9901_0]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h9836, h9881, hc01, hc14, hlam, hphi, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h8056, hlam, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [hlam, p9901_0]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h9836, hlam, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h9874, hlam, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h6681, h8057, h8058, h9878, h9882, h9883, h9893, h9895, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h8057, hlam, p9901_0]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h8057, h8058, h9878, h9882, h9895, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [hlam, p9901_0]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h9876, hlam, p9901_0]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h8058, h9878, h9882, h9895, hc01, hc12, hlam, hphi, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h8057, h8058, h9878, h9882, h9893, h9895, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h4610, h8058, h9878, h9882, h9895, hc01, hc12, hlam, hphi, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [h6681, h8058, h9878, h9882, h9895, hc01, hc12, hlam, hphi, p9901_1]
                            · have p9901_0 := h9901c.1
                              have p9901_1 := h9901c.2.1
                              have p9901_2 := h9901c.2.2.1
                              have p9901_3 := h9901c.2.2.2
                              linarith only [hlam, p9901_0]
                · linarith only [h4610, h9836, h9881, h9882, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9928 | h9928
                · linarith only [h4610, h9874, h9881, h9928, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9930 | h9930
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9931 | h9931
                    · linarith only [h8056, h9881, h9931, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9933 | h9933
                      · linarith only [h8057, h8058, h9880, h9928, h9931, h9933, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9935 | h9935
                        · linarith only [h4610, h8057, h8058, h9836, h9876, h9880, h9935, hc01, hc12, hlam, hphi]
                        · linarith only [h8057, h8058, h9881, h9930, h9931, h9935, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9938 | h9938
                    · linarith only [h8056, h8058, h9880, h9938, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9940 | h9940
                      · linarith only [h8057, h8058, h9880, h9928, h9938, h9940, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9942 | h9942
                        · linarith only [h8057, h8058, h9880, h9930, h9942, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9944 | h9944
                          · linarith only [h4610, h9881, h9930, h9944, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h4610, h9881, h9944, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9947 | h9947
              · linarith only [h4610, h9836, h9878, h9880, h9947, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9949 | h9949
                · linarith only [h4610, h9874, h9879, h9880, h9947, h9949, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9951 | h9951
                  · linarith only [h4610, h9836, h9876, h9879, h9880, h9951, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9953 | h9953
                    · linarith only [h4610, h8056, h9947, h9953, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9955 | h9955
                      · linarith only [h0, h4610, h8057, h9880, h9949, h9953, h9955, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9957 | h9957
                        · linarith only [h0, h8057, h9876, h9880, h9955, h9957, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9959 | h9959
                          · linarith only [h0, h8057, h9880, h9953, h9957, h9959, hc23, hc34, hlam, hphi]
                          · linarith only [h4610, h9947, h9959, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h8057, h9879, hlam]
        · linarith only [h0, h8056, h9878, hlam]

set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8057 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 2 5 (by decide) (by decide) with h8058 | h8058
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h8057 h8058
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h8057 h8058

set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8057 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 2 5 (by decide) (by decide) with h9964 | h9964
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9965 | h9965
    · linarith only [h8056, h8057, h9965, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9967 | h9967
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9968 | h9968
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9969 | h9969
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9970 | h9970
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9971 | h9971
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9972 | h9972
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9973 | h9973
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9974 | h9974
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9975 | h9975
                      · linarith only [h6681, h8056, h8057, h9965, h9970, h9975, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9977 | h9977
                        · linarith only [h8056, h8057, h9969, h9972, h9975, h9977, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h8056, h8057, h9967, h9969, h9972, h9975, h9977, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h6681, h9968, h9974, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h9965, h9967, h9972, h9973, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9982 | h9982
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9983 | h9983
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9984 | h9984
                      · linarith only [h8056, h8057, h9970, h9984, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9986 | h9986
                        · linarith only [h8056, h8057, h9970, h9986, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h8056, h8057, h9967, h9970, h9986, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h8056, h8057, h9967, h9968, h9970, h9983, hlam]
                  · linarith only [h8056, h8057, h9967, h9970, h9982, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h8057, h9964, h9970, h9971, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9992 | h9992
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9993 | h9993
                · linarith only [h9965, h9967, h9969, h9970, h9993, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9995 | h9995
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9996 | h9996
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9997 | h9997
                      · linarith only [h8056, h9993, h9997, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9999 | h9999
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10000 | h10000
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10001 | h10001
                            · rcases h0bigk with h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [hlam, p10002_0]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h0, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h4610, hlam, p10002_0]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h6681, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h7494, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h0, h9970, h9997, hc01, hc34, hlam, hphi, ht12, ht23, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [hlam, p10002_0]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h0, h10001, h8056, h9970, h9997, h9999, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h8057, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h0, h7494, h9970, h9997, hc01, hc34, hlam, hphi, ht12, ht23, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h0, h8056, h9970, h9997, hc01, hc34, hlam, hphi, ht12, ht23, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h8056, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [hlam, p10002_0]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h9965, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h0, h7494, h8056, h9970, h9997, hc01, hc34, hlam, hphi, ht12, ht23, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                rcases p10002_3 (m.d 0 1) (by simp) with h10018 | h10018
                                · linarith only [h10018, h6681, hlam]
                                · rcases p10002_3 (m.d 0 2) (by simp) with h10020 | h10020
                                  · linarith only [h10020, h8057, hlam]
                                  · linarith only [h0, h10020, hlam]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h10001, h8056, h9999, hc45, hlam, hphi, ht0b, ht5b, p10002_1, u0elo3]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h10001, h8056, h9999, hc45, hlam, hphi, ht0b, ht5b, p10002_1, u0elo3]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [hlam, p10002_0]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                rcases p10002_3 (m.d 0 1) (by simp) with h10026 | h10026
                                · linarith only [h10026, h6681, hlam]
                                · rcases p10002_3 (m.d 0 2) (by simp) with h10028 | h10028
                                  · linarith only [h10028, h8057, hlam]
                                  · linarith only [h10028, h9964, hlam]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h0, h9964, h9970, h9997, hc01, hc34, hlam, hphi, ht12, ht23, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h9964, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h9967, hlam, p10002_0]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h9968, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [hlam, p10002_0]
                            · linarith only [h0, h10001, h8056, h9970, h9997, h9999, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h0, h10000, h8056, h9967, h9968, h9970, hlam]
                        · linarith only [h0, h8056, h9967, h9970, h9997, h9999, hc23, hc34, hlam, hphi]
                    · linarith only [h6681, h9968, h9996, hlam]
                  · linarith only [h0, h4610, h8056, h9967, h9970, h9995, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h9964, h9992, hlam]
          · linarith only [h0, h8056, h9969, hlam]
        · linarith only [h8056, h8057, h9967, h9968, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10044 | h10044
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10045 | h10045
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10046 | h10046
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10047 | h10047
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10048 | h10048
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10049 | h10049
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10050 | h10050
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10051 | h10051
                      · linarith only [h10046, h10051, h8056, h8057, h9965, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10053 | h10053
                        · linarith only [h10045, h10048, h10051, h10053, h4610, h8056, h8057, h9967, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10055 | h10055
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10056 | h10056
                            · rcases h0bigk with h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [hlam, p10057_0]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h0, hlam, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h4610, hlam, p10057_0]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h6681, hlam, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h7494, hlam, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h10045, h10048, h10051, h8057, hc01, hc12, hlam, hphi, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [hlam, p10057_0]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h10045, h10048, h10051, h4610, h8057, hc01, hc12, hlam, hphi, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h8057, hlam, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h10045, h10048, h10051, h8057, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h10049, h9967, hc01, hc15, hlam, hphi, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h8056, hlam, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [hlam, p10057_0]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h9965, hlam, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h9967, hlam, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h10045, h10048, h10051, h8057, hc01, hc12, hlam, hphi, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h10045, h10048, h10051, h10053, h8057, h9964, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h10045, h10048, h10051, h4610, h8057, hc01, hc12, hlam, hphi, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [hlam, p10057_0]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h10045, h10048, h10051, h4610, h8057, h9967, hc01, hc12, hlam, hphi, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h10045, h10048, h10051, h8057, h9964, hc01, hc12, hlam, hphi, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h9964, hlam, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h10045, h10048, h10051, h4610, h8057, h9964, hc01, hc12, hlam, hphi, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [h10044, hlam, p10057_1]
                              · have p10057_0 := h10057c.1
                                have p10057_1 := h10057c.2.1
                                have p10057_2 := h10057c.2.2.1
                                have p10057_3 := h10057c.2.2.2
                                linarith only [hlam, p10057_0]
                            · linarith only [h10051, h10056, h8056, h8057, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h10044, h10055, h8057, h9964, hlam]
                    · linarith only [h10044, h10050, h6681, h8057, h9964, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h10048, h10049, h8056, h8057, h9965, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10087 | h10087
                  · linarith only [h10048, h10087, h4610, h9967, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10089 | h10089
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10090 | h10090
                      · linarith only [h10048, h10090, h8056, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10092 | h10092
                        · linarith only [h10046, h10087, h10092, h4610, h8056, h8057, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10094 | h10094
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10095 | h10095
                            · rcases h0bigk with h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c | h10096c
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [hlam, p10096_0]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h0, hlam, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h4610, hlam, p10096_0]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h6681, hlam, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h7494, hlam, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h10046, h8057, hc01, hc12, hlam, hphi, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [hlam, p10096_0]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h10046, h4610, h8057, hc01, hc12, hlam, hphi, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h8057, hlam, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h10046, h8057, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h10087, h4610, hc01, hc35, hlam, hphi, ht12, ht23, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h8056, hlam, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [hlam, p10096_0]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h9965, hlam, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h9967, hlam, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h10046, h8057, hc01, hc12, hlam, hphi, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h10046, h10092, h8057, h9964, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h10046, h4610, h8057, hc01, hc12, hlam, hphi, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [hlam, p10096_0]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h10046, h4610, h8057, h9967, hc01, hc12, hlam, hphi, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h10046, h8057, h9964, hc01, hc12, hlam, hphi, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h9964, hlam, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h10046, h4610, h8057, h9964, hc01, hc12, hlam, hphi, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [h10044, hlam, p10096_1]
                              · have p10096_0 := h10096c.1
                                have p10096_1 := h10096c.2.1
                                have p10096_2 := h10096c.2.2.1
                                have p10096_3 := h10096c.2.2.2
                                linarith only [hlam, p10096_0]
                            · linarith only [h10048, h10095, h4610, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h10044, h10094, h8057, h9964, hlam]
                    · linarith only [h10044, h10046, h10089, h8057, h9964, hlam]
              · linarith only [h10046, h10047, h8057, h9964, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10126 | h10126
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10127 | h10127
                · linarith only [h10045, h10046, h10127, h4610, h9965, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10129 | h10129
                  · linarith only [h10045, h10046, h10129, h4610, h9967, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10131 | h10131
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10132 | h10132
                      · linarith only [h10127, h10132, h4610, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10134 | h10134
                        · linarith only [h10129, h10134, h4610, h8056, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10136 | h10136
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10137 | h10137
                            · rcases h0bigk with h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c | h10138c
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [hlam, p10138_0]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h0, hlam, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h4610, hlam, p10138_0]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h6681, hlam, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h7494, hlam, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h0, h10046, h10132, hc01, hc34, hlam, hphi, ht12, ht23, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [hlam, p10138_0]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h0, h10046, h10132, hc03, hc34, hlam, hphi, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h8057, hlam, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h0, h10046, h10132, h7494, hc01, hc34, hlam, hphi, ht12, ht23, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h10046, h10126, h10129, h10132, h4610, hc01, hc34, hlam, hphi, ht12, ht23, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h8056, hlam, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [hlam, p10138_0]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h9965, hlam, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h9967, hlam, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                rcases p10138_3 (m.d 0 1) (by simp) with h10154 | h10154
                                · linarith only [h10154, h6681, hlam]
                                · rcases p10138_3 (m.d 0 2) (by simp) with h10156 | h10156
                                  · linarith only [h10156, h8057, hlam]
                                  · linarith only [h0, h10156, hlam]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h10134, h9964, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10138_1, u0elo3]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                rcases p10138_3 (m.d 0 1) (by simp) with h10160 | h10160
                                · linarith only [h10160, h6681, hlam]
                                · rcases p10138_3 (m.d 0 2) (by simp) with h10162 | h10162
                                  · linarith only [h10162, h8057, hlam]
                                  · linarith only [h10162, h8056, hlam]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [hlam, p10138_0]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                rcases p10138_3 (m.d 0 1) (by simp) with h10166 | h10166
                                · linarith only [h10166, h6681, hlam]
                                · rcases p10138_3 (m.d 0 2) (by simp) with h10168 | h10168
                                  · linarith only [h10168, h8057, hlam]
                                  · linarith only [h10168, h9964, hlam]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h10046, h10126, h10132, h7494, hc01, hc34, hlam, hphi, ht12, ht23, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h9964, hlam, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h10046, h10126, h10132, h4610, h7494, hc01, hc34, hlam, hphi, ht12, ht23, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [h10044, hlam, p10138_1]
                              · have p10138_0 := h10138c.1
                                have p10138_1 := h10138c.2.1
                                have p10138_2 := h10138c.2.2.1
                                have p10138_3 := h10138c.2.2.2
                                linarith only [hlam, p10138_0]
                            · linarith only [h0, h10046, h10132, h10137, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h10044, h10046, h10136, h9964, hlam]
                    · linarith only [h0, h10044, h10046, h10131, h6681, h9964, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h10126, h9964, hlam]
          · linarith only [h0, h10045, h8056, hlam]
        · linarith only [h10044, h8057, h9964, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10182 | h10182
    · linarith only [h10182, h8056, h8057, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10184 | h10184
      · linarith only [h10184, h8056, h9964, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10186 | h10186
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10187 | h10187
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10188 | h10188
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10189 | h10189
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10190 | h10190
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10191 | h10191
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10192 | h10192
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10193 | h10193
                      · linarith only [h10182, h10193, h4610, h8056, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10195 | h10195
                        · linarith only [h10184, h10187, h10190, h10193, h10195, h4610, h8056, h8057, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10197 | h10197
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10198 | h10198
                            · rcases h0bigk with h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c | h10199c
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [hlam, p10199_0]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h0, hlam, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h4610, hlam, p10199_0]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h6681, hlam, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h7494, hlam, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10187, h10190, h10193, h10197, h9964, hc01, hc12, hlam, hphi, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [hlam, p10199_0]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10187, h10190, h10193, h10197, h4610, h9964, hc01, hc12, hlam, hphi, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h8057, hlam, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h9964, hlam, p10199_0]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10187, h10190, h10193, h10197, h8056, h9964, hc01, hc12, hlam, hphi, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h8056, hlam, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [hlam, p10199_0]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10182, hlam, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10184, hlam, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10187, h10190, h10193, h8057, hc01, hc12, hlam, hphi, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10187, h10190, h10193, h8056, h8057, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10187, h10190, h10193, h4610, h8057, hc01, hc12, hlam, hphi, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [hlam, p10199_0]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10187, h10190, h10193, h8056, h8057, h9964, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10187, h10190, h10193, h10197, h9964, hc01, hc12, hlam, hphi, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10187, h10190, h10193, h10197, h8056, h9964, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10187, h10190, h10193, h10197, h4610, h9964, hc01, hc12, hlam, hphi, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [h10186, hlam, p10199_1]
                              · have p10199_0 := h10199c.1
                                have p10199_1 := h10199c.2.1
                                have p10199_2 := h10199c.2.2.1
                                have p10199_3 := h10199c.2.2.2
                                linarith only [hlam, p10199_0]
                            · linarith only [h10186, h10193, h10198, h8057, hlam]
                          · linarith only [h10186, h10197, h8057, hlam]
                    · linarith only [h10186, h10192, h6681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h10182, h10190, h10191, h8056, h8057, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10229 | h10229
                  · linarith only [h10184, h10190, h10229, h4610, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10231 | h10231
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10232 | h10232
                      · linarith only [h10190, h10232, h8056, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10234 | h10234
                        · linarith only [h10229, h10234, h4610, h8056, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10236 | h10236
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10237 | h10237
                            · rcases h0bigk with h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c | h10238c
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [hlam, p10238_0]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h0, hlam, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h4610, hlam, p10238_0]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h6681, hlam, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h7494, hlam, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10188, h10236, h9964, hc01, hc12, hlam, hphi, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [hlam, p10238_0]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10188, h10236, h4610, h9964, hc01, hc12, hlam, hphi, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h8057, hlam, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h9964, hlam, p10238_0]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10188, h10236, h8056, h9964, hc01, hc12, hlam, hphi, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h8056, hlam, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [hlam, p10238_0]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10182, hlam, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10184, hlam, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10188, h8057, hc01, hc12, hlam, hphi, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10188, h8056, h8057, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10188, h4610, h8057, hc01, hc12, hlam, hphi, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [hlam, p10238_0]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10188, h8056, h8057, h9964, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10188, h10236, h9964, hc01, hc12, hlam, hphi, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10188, h10236, h8056, h9964, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10188, h10236, h4610, h9964, hc01, hc12, hlam, hphi, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [h10186, hlam, p10238_1]
                              · have p10238_0 := h10238c.1
                                have p10238_1 := h10238c.2.1
                                have p10238_2 := h10238c.2.2.1
                                have p10238_3 := h10238c.2.2.2
                                linarith only [hlam, p10238_0]
                            · linarith only [h10186, h10188, h10190, h10237, h8057, hlam]
                          · linarith only [h10186, h10236, h8057, hlam]
                    · linarith only [h10186, h10188, h10231, h8057, hlam]
              · linarith only [h10188, h10189, h8056, h8057, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10268 | h10268
              · linarith only [h10188, h10268, h8056, h9964, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10270 | h10270
                · linarith only [h10182, h10187, h10188, h10270, h4610, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10272 | h10272
                  · linarith only [h10184, h10270, h10272, hc03, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10274 | h10274
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10275 | h10275
                      · linarith only [h10270, h10275, h8056, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10277 | h10277
                        · linarith only [h0, h10188, h10272, h10275, h10277, h7494, h8056, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10279 | h10279
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10280 | h10280
                            · rcases h0bigk with h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [hlam, p10281_0]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h0, hlam, p10281_1]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h4610, hlam, p10281_0]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h6681, hlam, p10281_1]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h7494, hlam, p10281_1]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h0, h10268, h10275, h10279, hc01, hc34, hlam, hphi, ht12, ht23, p10281_1]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [hlam, p10281_0]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h0, h10268, h10275, h10279, hc03, hc34, hlam, hphi, p10281_1]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h8057, hlam, p10281_1]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h9964, hlam, p10281_0]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h0, h10268, h10275, h10279, h8056, hc01, hc34, hlam, hphi, ht12, ht23, p10281_1]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h8056, hlam, p10281_1]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [hlam, p10281_0]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h10182, hlam, p10281_1]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h10184, hlam, p10281_1]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                rcases p10281_3 (m.d 0 1) (by simp) with h10297 | h10297
                                · linarith only [h10297, h6681, hlam]
                                · rcases p10281_3 (m.d 0 2) (by simp) with h10299 | h10299
                                  · linarith only [h10299, h8057, hlam]
                                  · linarith only [h0, h10299, hlam]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h8056, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10281_1, u0elo3]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                rcases p10281_3 (m.d 0 1) (by simp) with h10303 | h10303
                                · linarith only [h10303, h6681, hlam]
                                · rcases p10281_3 (m.d 0 2) (by simp) with h10305 | h10305
                                  · linarith only [h10305, h8057, hlam]
                                  · linarith only [h10305, h8056, hlam]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [hlam, p10281_0]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h8056, h9964, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10281_1, u0elo3]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                rcases p10281_3 (m.d 0 1) (by simp) with h10310 | h10310
                                · linarith only [h10310, h7494, hlam]
                                · rcases p10281_3 (m.d 0 2) (by simp) with h10312 | h10312
                                  · linarith only [h10312, h9964, hlam]
                                  · linarith only [h0, h10312, hlam]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h8056, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10281_1, u0elo4]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                rcases p10281_3 (m.d 0 1) (by simp) with h10316 | h10316
                                · linarith only [h10316, h7494, hlam]
                                · rcases p10281_3 (m.d 0 2) (by simp) with h10318 | h10318
                                  · linarith only [h10318, h9964, hlam]
                                  · linarith only [h10318, h8056, hlam]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [h10186, hlam, p10281_1]
                              · have p10281_0 := h10281c.1
                                have p10281_1 := h10281c.2.1
                                have p10281_2 := h10281c.2.2.1
                                have p10281_3 := h10281c.2.2.2
                                linarith only [hlam, p10281_0]
                            · linarith only [h10186, h10188, h10275, h10280, h6681, hlam]
                          · linarith only [h10186, h10188, h10279, h6681, hlam]
                    · linarith only [h10186, h10274, h6681, hlam]
          · linarith only [h0, h10187, h8056, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10327 | h10327
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10328 | h10328
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10329 | h10329
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10330 | h10330
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10331 | h10331
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10332 | h10332
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10333 | h10333
                      · linarith only [h10182, h10333, h4610, h8056, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10335 | h10335
                        · linarith only [h10186, h10327, h10330, h10332, h10335, h8056, h8057, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10337 | h10337
                          · linarith only [h10186, h10333, h10337, h8056, h8057, hc23, hc34, hlam, hphi]
                          · linarith only [h10327, h10330, h10332, h10337, h8056, h8057, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h10328, h10332, h8056, h8057, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h10182, h10330, h10331, h4610, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10342 | h10342
                  · linarith only [h10184, h10330, h10342, h4610, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10344 | h10344
                    · linarith only [h10186, h10330, h10344, h8056, h8057, hc23, hc34, hlam, hphi]
                    · linarith only [h10328, h10344, h8056, h8057, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h10328, h10329, h8056, h8057, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10348 | h10348
              · linarith only [h10328, h10348, h8056, h9964, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10350 | h10350
                · linarith only [h10182, h10327, h10328, h10350, h4610, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10352 | h10352
                  · linarith only [h10184, h10350, h10352, h4610, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10354 | h10354
                    · linarith only [h10186, h10350, h10354, h8056, h8057, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10356 | h10356
                      · linarith only [h10354, h10356, h6681, h8056, h8057, hc34, hc45, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10358 | h10358
                        · linarith only [h10352, h10354, h10358, h4610, h6681, h8056, h8057, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10360 | h10360
                          · linarith only [h10354, h10356, h10360, h6681, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h10360, h8056, h8057, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h10327, h8056, h8057, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 2 4 (by decide) (by decide) with h8057 | h8057
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h8057
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h8057

end R2N4
