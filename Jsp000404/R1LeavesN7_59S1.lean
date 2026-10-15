import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_59S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3546000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_R_M_IR_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h749 | h749
  · rcases m.htr 0 1 4 (by decide) (by decide) with h750 | h750
    · rcases m.htr 0 1 5 (by decide) (by decide) with h751 | h751
      · rcases m.htr 0 2 3 (by decide) (by decide) with h752 | h752
        · rcases m.htr 0 2 4 (by decide) (by decide) with h753 | h753
          · rcases m.htr 0 2 5 (by decide) (by decide) with h754 | h754
            · rcases m.htr 0 3 4 (by decide) (by decide) with h755 | h755
              · rcases m.htr 0 3 5 (by decide) (by decide) with h756 | h756
                · rcases m.htr 0 4 5 (by decide) (by decide) with h757 | h757
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h758 | h758
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h759 | h759
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h760 | h760
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h761 | h761
                          · linarith only [h749, h761, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h755, h761, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h0, h751, h760, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h751, h759, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h751, h758, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h767 | h767
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h768 | h768
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h769 | h769
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h770 | h770
                          · linarith only [h749, h770, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h755, h770, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h0, h749, h756, h769, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h749, h755, h768, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h749, h755, h767, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h755, h756, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h777 | h777
                · linarith only [h755, h777, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h779 | h779
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h780 | h780
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h781 | h781
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h782 | h782
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h783 | h783
                          · linarith only [h749, h755, h783, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h785 | h785
                            · linarith only [h0, h749, h785, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h787 | h787
                              · linarith only [h0, h750, h787, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                              · linarith only [h0, h750, h779, h783, h787, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                        · linarith only [h0, h749, h754, h780, h782, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi2]
                      · linarith only [h0, h749, h780, h781, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h749, h780, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h793 | h793
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h794 | h794
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h795 | h795
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h796 | h796
                          · linarith only [h749, h755, h796, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h798 | h798
                            · linarith only [h749, h777, h798, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h800 | h800
                              · linarith only [h750, h779, h800, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h802 | h802
                                · linarith only [h749, h755, h793, h802, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h804 | h804
                                  · linarith only [h749, h777, h793, h804, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h806 | h806
                                    · linarith only [h750, h779, h794, h806, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h808 | h808
                                      · linarith only [h750, h779, h793, h796, h808, hc34, hlam, hphi, u3ehi2]
                                      · linarith only [h749, h755, h793, h808, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h0, h751, h795, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h751, h794, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h751, h793, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h751, h754, hlam]
          · linarith only [h0, h750, h753, hlam]
        · linarith only [h0, h749, h752, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h817 | h817
        · rcases m.htr 0 2 4 (by decide) (by decide) with h818 | h818
          · rcases m.htr 0 2 5 (by decide) (by decide) with h819 | h819
            · rcases m.htr 0 3 4 (by decide) (by decide) with h820 | h820
              · rcases m.htr 0 3 5 (by decide) (by decide) with h821 | h821
                · linarith only [h749, h751, h821, hlam]
                · linarith only [h820, h821, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h824 | h824
                · linarith only [h820, h824, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h826 | h826
                  · linarith only [h750, h751, h826, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h828 | h828
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h829 | h829
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h830 | h830
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h831 | h831
                          · linarith only [h749, h831, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h833 | h833
                            · linarith only [h750, h751, h824, h830, h831, h833, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h749, h751, h828, h833, hc35, hlam, hphi, u3ehi2]
                        · linarith only [h0, h749, h819, h828, h830, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                      · linarith only [h0, h749, h828, h829, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h749, h828, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h839 | h839
              · rcases m.htr 0 3 5 (by decide) (by decide) with h840 | h840
                · linarith only [h749, h751, h840, hlam]
                · linarith only [h839, h840, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h843 | h843
                · linarith only [h839, h843, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h845 | h845
                  · linarith only [h0, h750, h819, h845, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h847 | h847
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h848 | h848
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h849 | h849
                        · linarith only [h0, h749, h819, h847, h849, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h749, h847, h849, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h749, h847, h848, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h749, h847, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h750, h818, hlam]
        · linarith only [h0, h749, h817, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h856 | h856
      · rcases m.htr 0 2 3 (by decide) (by decide) with h857 | h857
        · rcases m.htr 0 2 4 (by decide) (by decide) with h858 | h858
          · rcases m.htr 0 2 5 (by decide) (by decide) with h859 | h859
            · rcases m.htr 0 3 4 (by decide) (by decide) with h860 | h860
              · linarith only [h749, h750, h860, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h862 | h862
                · linarith only [h860, h862, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h864 | h864
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h865 | h865
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h866 | h866
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h867 | h867
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h868 | h868
                          · linarith only [h749, h750, h858, h860, h868, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                          · linarith only [h749, h750, h865, h868, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h749, h750, h865, h866, h867, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h858, h866, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h749, h865, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h749, h750, h864, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h0, h856, h859, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h876 | h876
            · rcases m.htr 0 3 4 (by decide) (by decide) with h877 | h877
              · linarith only [h0, h749, h858, h877, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h879 | h879
                · linarith only [h877, h879, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h881 | h881
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h882 | h882
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h883 | h883
                      · linarith only [h858, h876, h883, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h749, h882, h883, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h749, h882, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h749, h750, h881, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h0, h856, h876, hlam]
        · linarith only [h0, h749, h857, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h890 | h890
        · rcases m.htr 0 2 4 (by decide) (by decide) with h891 | h891
          · rcases m.htr 0 2 5 (by decide) (by decide) with h892 | h892
            · rcases m.htr 0 3 4 (by decide) (by decide) with h893 | h893
              · linarith only [h749, h750, h893, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h895 | h895
                · linarith only [h893, h895, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h897 | h897
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h898 | h898
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h899 | h899
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h900 | h900
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h901 | h901
                          · linarith only [h749, h856, h891, h893, h897, h901, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                          · linarith only [h749, h750, h898, h901, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h749, h750, h892, h898, h899, h900, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                      · linarith only [h0, h749, h891, h898, h899, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                    · linarith only [h0, h749, h898, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h749, h750, h897, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h908 | h908
              · linarith only [h749, h750, h908, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h910 | h910
                · linarith only [h908, h910, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h912 | h912
                  · linarith only [h891, h892, h912, hlam]
                  · linarith only [h749, h750, h912, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h915 | h915
            · rcases m.htr 0 3 4 (by decide) (by decide) with h916 | h916
              · linarith only [h0, h749, h891, h916, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h918 | h918
                · linarith only [h916, h918, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h920 | h920
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h921 | h921
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h922 | h922
                      · linarith only [h891, h915, h922, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h749, h921, h922, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h749, h921, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h749, h856, h891, h915, h920, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h927 | h927
              · linarith only [h0, h749, h891, h927, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h929 | h929
                · linarith only [h927, h929, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h931 | h931
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h932 | h932
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h933 | h933
                      · linarith only [h0, h749, h891, h932, h933, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h749, h932, h933, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h749, h932, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h749, h750, h931, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h0, h749, h890, hlam]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h939 | h939
    · rcases m.htr 0 1 5 (by decide) (by decide) with h940 | h940
      · rcases m.htr 0 2 3 (by decide) (by decide) with h941 | h941
        · rcases m.htr 0 2 4 (by decide) (by decide) with h942 | h942
          · rcases m.htr 0 2 5 (by decide) (by decide) with h943 | h943
            · rcases m.htr 0 3 4 (by decide) (by decide) with h944 | h944
              · rcases m.htr 0 3 5 (by decide) (by decide) with h945 | h945
                · rcases m.htr 0 4 5 (by decide) (by decide) with h946 | h946
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h947 | h947
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h948 | h948
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h949 | h949
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h950 | h950
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h951 | h951
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h952 | h952
                              · linarith only [h939, h952, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h749, h939, h941, h946, h950, h952, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · linarith only [h749, h940, h951, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h749, h940, h950, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h749, h939, h946, h947, h949, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h749, h939, h946, h947, h948, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h939, h941, h946, h947, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h960 | h960
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h961 | h961
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h962 | h962
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h963 | h963
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h964 | h964
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h965 | h965
                              · linarith only [h939, h946, h965, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h967 | h967
                                · linarith only [h941, h967, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                                · linarith only [h749, h940, h960, h963, h965, h967, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h749, h940, h964, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h749, h940, h941, h944, h962, h963, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
                        · linarith only [h749, h940, h960, h962, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h749, h940, h960, h961, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h940, h960, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h944, h945, hc35, hlam, hphi, u3ehi3]
              · linarith only [h749, h939, h944, hlam]
            · linarith only [h0, h940, h943, hlam]
          · linarith only [h749, h939, h941, h942, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h979 | h979
          · rcases m.htr 0 2 5 (by decide) (by decide) with h980 | h980
            · rcases m.htr 0 3 4 (by decide) (by decide) with h981 | h981
              · rcases m.htr 0 3 5 (by decide) (by decide) with h982 | h982
                · rcases m.htr 0 4 5 (by decide) (by decide) with h983 | h983
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h984 | h984
                    · linarith only [h941, h980, h984, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h0, h939, h983, h984, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h987 | h987
                    · linarith only [h0, h940, h941, h987, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                    · linarith only [h0, h940, h987, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h981, h982, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h939, h941, h981, hlam]
            · linarith only [h0, h940, h980, hlam]
          · linarith only [h0, h939, h979, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h994 | h994
        · rcases m.htr 0 2 4 (by decide) (by decide) with h995 | h995
          · rcases m.htr 0 2 5 (by decide) (by decide) with h996 | h996
            · rcases m.htr 0 3 4 (by decide) (by decide) with h997 | h997
              · rcases m.htr 0 3 5 (by decide) (by decide) with h998 | h998
                · rcases m.htr 0 4 5 (by decide) (by decide) with h999 | h999
                  · linarith only [h939, h940, h999, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1001 | h1001
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1002 | h1002
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1003 | h1003
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1004 | h1004
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1005 | h1005
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1006 | h1006
                              · linarith only [h1006, h939, h999, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h1004, h1006, h939, h940, hc45, hlam, hphi, ht34, u3ehi3]
                            · linarith only [h1005, h994, h998, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                          · linarith only [h1004, h749, h998, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h0, h1003, h996, hlam]
                      · linarith only [h0, h1002, h995, hlam]
                    · linarith only [h0, h1001, h994, hlam]
                · linarith only [h997, h998, hc35, hlam, hphi, u3ehi3]
              · linarith only [h749, h939, h997, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1016 | h1016
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1017 | h1017
                · linarith only [h1017, h994, h996, hlam]
                · linarith only [h1016, h1017, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1016, h749, h939, hlam]
          · linarith only [h0, h939, h995, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1022 | h1022
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1023 | h1023
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1024 | h1024
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1025 | h1025
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1026 | h1026
                  · linarith only [h1026, h939, h940, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1028 | h1028
                    · linarith only [h1023, h1028, h994, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1030 | h1030
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1031 | h1031
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1032 | h1032
                          · linarith only [h0, h1028, h1032, h939, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1024, h1028, h1031, h1032, h939, h940, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h0, h1023, h1024, h1031, h939, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · linarith only [h0, h1022, h1030, hlam]
                · linarith only [h1024, h1025, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h1024, h939, h994, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1039 | h1039
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1040 | h1040
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1041 | h1041
                  · linarith only [h0, h1023, h1041, h939, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1043 | h1043
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1044 | h1044
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1045 | h1045
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1046 | h1046
                          · linarith only [h0, h1043, h1046, h939, h994, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h1039, h1043, h1046, h994, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1039, h1043, h1045, h939, h994, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h1039, h1043, h1044, h939, h994, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1051 | h1051
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1052 | h1052
                        · linarith only [h0, h1023, h1039, h1043, h1052, h939, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1054 | h1054
                          · linarith only [h0, h1043, h1054, h939, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1039, h1054, h749, h939, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1022, h1051, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1039, h1040, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h1039, h939, h994, hlam]
          · linarith only [h0, h1022, h939, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1061 | h1061
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1062 | h1062
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1063 | h1063
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1064 | h1064
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1065 | h1065
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1066 | h1066
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1067 | h1067
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1068 | h1068
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1069 | h1069
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1070 | h1070
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1071 | h1071
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1072 | h1072
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1073 | h1073
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1074 | h1074
                                · linarith only [h1062, h1074, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                                · linarith only [h1065, h1074, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h1061, h1072, h1073, h939, hc45, hlam, hphi, ht34, u3ehi4]
                            · linarith only [h1061, h1071, h1072, h939, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h1062, h1065, h1071, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                        · linarith only [h1061, h1069, h1070, h939, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h1061, h1063, h1069, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
                    · linarith only [h0, h1061, h1062, h1068, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
                  · linarith only [h1061, h1067, h939, hlam]
                · linarith only [h1065, h1066, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1085 | h1085
                · linarith only [h1065, h1085, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1061, h1085, h749, hlam]
            · linarith only [h0, h1061, h1064, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1089 | h1089
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1090 | h1090
              · linarith only [h1062, h1063, h1090, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1092 | h1092
                · linarith only [h1090, h1092, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1061, h1092, h749, hlam]
            · linarith only [h1061, h1062, h1089, h749, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1096 | h1096
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1097 | h1097
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1098 | h1098
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1099 | h1099
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1100 | h1100
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1101 | h1101
                    · linarith only [h1062, h1097, h1101, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h0, h1061, h1101, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h1061, h1100, h939, hlam]
                · linarith only [h1098, h1099, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1062, h1096, h1098, hlam]
            · linarith only [h1061, h1096, h1097, h939, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1108 | h1108
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1109 | h1109
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1110 | h1110
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1111 | h1111
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1112 | h1112
                    · linarith only [h1062, h1108, h1112, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h0, h1061, h1112, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h1061, h1096, h1111, hlam]
                · linarith only [h1109, h1110, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1117 | h1117
                · linarith only [h1109, h1117, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1061, h1117, h749, hlam]
            · linarith only [h0, h1061, h1108, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1121 | h1121
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1122 | h1122
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1123 | h1123
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1124 | h1124
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1125 | h1125
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1126 | h1126
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1127 | h1127
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1128 | h1128
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1129 | h1129
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1130 | h1130
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1131 | h1131
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1132 | h1132
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1133 | h1133
                                · linarith only [h1121, h1133, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                                · linarith only [h1124, h1133, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h1121, h1124, h1126, h1132, h939, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h1121, h1125, h1131, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                          · linarith only [h1124, h1130, h749, hlam]
                        · linarith only [h0, h1123, h1129, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1122, h1128, hlam]
                    · linarith only [h0, h1121, h1127, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1142 | h1142
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1143 | h1143
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1144 | h1144
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1145 | h1145
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1146 | h1146
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1147 | h1147
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1148 | h1148
                                · linarith only [h1121, h1148, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                                · linarith only [h1124, h1148, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1151 | h1151
                                · linarith only [h1121, h1151, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                                · linarith only [h1124, h1151, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                            · linarith only [h1124, h1146, h749, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h1124, h1145, h749, hlam]
                        · linarith only [h0, h1123, h1144, hlam]
                      · linarith only [h0, h1122, h1143, hlam]
                    · linarith only [h0, h1121, h1142, hlam]
                · linarith only [h1124, h1125, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1160 | h1160
                · linarith only [h1124, h1160, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1162 | h1162
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1163 | h1163
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1164 | h1164
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1165 | h1165
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1166 | h1166
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1167 | h1167
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1168 | h1168
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1169 | h1169
                                · linarith only [h1121, h1124, h1169, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1171 | h1171
                                  · linarith only [h1121, h1160, h1171, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1173 | h1173
                                    · linarith only [h1122, h1173, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                    · linarith only [h1162, h1169, h1173, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                              · linarith only [h1162, h1168, h939, hlam]
                            · linarith only [h1166, h1167, hc35, hlam, hphi, u3ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1178 | h1178
                            · linarith only [h1166, h1178, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1180 | h1180
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1181 | h1181
                                · linarith only [h1121, h1166, h1181, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1183 | h1183
                                  · linarith only [h1121, h1183, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1185 | h1185
                                    · linarith only [h1122, h1185, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                    · linarith only [h1162, h1181, h1185, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                              · linarith only [h1162, h1180, h939, hlam]
                        · linarith only [h0, h1123, h1165, hlam]
                      · linarith only [h0, h1122, h1164, hlam]
                    · linarith only [h0, h1121, h1163, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1192 | h1192
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1193 | h1193
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1194 | h1194
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1195 | h1195
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1196 | h1196
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1197 | h1197
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1198 | h1198
                                · linarith only [h1121, h1124, h1198, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1200 | h1200
                                  · linarith only [h1121, h1160, h1200, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1202 | h1202
                                    · linarith only [h1122, h1162, h1202, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1204 | h1204
                                      · linarith only [h1121, h1124, h1162, h1204, hc34, hlam, hphi, u3ehi2]
                                      · linarith only [h1121, h1124, h1192, h1195, h1197, h1204, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                              · linarith only [h1121, h1124, h1195, h1197, hc45, hlam, hphi, ht34, u3ehi2]
                            · linarith only [h1121, h1124, h1195, h1196, hc35, hlam, hphi, u3ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1209 | h1209
                            · linarith only [h1195, h1209, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1211 | h1211
                              · linarith only [h1121, h1124, h1162, h1195, h1211, hc34, hlam, hphi, u3ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1213 | h1213
                                · linarith only [h1121, h1195, h1211, h1213, h749, hc45, hlam, hphi, ht34, u3ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1215 | h1215
                                  · linarith only [h1121, h1195, h1211, h1215, h749, hc45, hlam, hphi, ht34, u3ehi4]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1217 | h1217
                                    · linarith only [h1122, h1211, h1217, h939, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1219 | h1219
                                      · linarith only [h1195, h1211, h1219, h749, hc34, hlam, hphi, u3ehi0]
                                      · linarith only [h1121, h1124, h1219, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h0, h1123, h1194, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1122, h1123, h1193, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
                    · linarith only [h0, h1121, h1192, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1225 | h1225
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1226 | h1226
                · linarith only [h1121, h1123, h1226, hlam]
                · linarith only [h1225, h1226, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1229 | h1229
                · linarith only [h1225, h1229, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1231 | h1231
                  · linarith only [h1122, h1123, h1231, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1233 | h1233
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1234 | h1234
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1235 | h1235
                        · linarith only [h1121, h1123, h1235, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1237 | h1237
                          · linarith only [h1121, h1225, h1233, h1235, h1237, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1239 | h1239
                            · linarith only [h1121, h1123, h1229, h1237, h1239, hc34, hlam, hphi, u3ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1241 | h1241
                              · linarith only [h1231, h1234, h1235, h1241, h939, hc01, hc25, hlam, hphi, ht12]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1243 | h1243
                                · linarith only [h1121, h1243, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1245 | h1245
                                  · linarith only [h0, h1122, h1235, h1243, h1245, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                                  · linarith only [h0, h1122, h1235, h1243, h1245, hc35, hlam, hphi, u3ehi2]
                      · linarith only [h0, h1122, h1234, hlam]
                    · linarith only [h0, h1121, h1233, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1250 | h1250
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1251 | h1251
              · linarith only [h1121, h1122, h1251, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1253 | h1253
                · linarith only [h1251, h1253, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1255 | h1255
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1256 | h1256
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1257 | h1257
                      · linarith only [h1121, h1122, h1257, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1259 | h1259
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1260 | h1260
                          · linarith only [h1121, h1122, h1251, h1256, h1257, h1260, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1262 | h1262
                            · linarith only [h1121, h1253, h1260, h1262, hc34, hlam, hphi, u3ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1264 | h1264
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1265 | h1265
                                · linarith only [h1121, h1260, h1265, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                                · linarith only [h0, h1121, h1257, h1265, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h0, h1121, h1255, h1257, h1264, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                        · linarith only [h0, h1250, h1259, hlam]
                    · linarith only [h0, h1121, h1256, hlam]
                  · linarith only [h1121, h1122, h1255, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1272 | h1272
              · linarith only [h1121, h1122, h1272, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1274 | h1274
                · linarith only [h1272, h1274, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1276 | h1276
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1277 | h1277
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1278 | h1278
                      · linarith only [h1121, h1122, h1278, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1280 | h1280
                        · linarith only [h1121, h1250, h1278, h1280, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1282 | h1282
                          · linarith only [h1272, h1277, h1278, h1282, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1284 | h1284
                            · linarith only [h1121, h1250, h1274, h1282, h1284, hc34, hlam, hphi, u3ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1286 | h1286
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1287 | h1287
                                · linarith only [h1121, h1282, h1287, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                                · linarith only [h0, h1121, h1278, h1287, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h1121, h1122, h1286, h939, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h0, h1121, h1277, hlam]
                  · linarith only [h1121, h1122, h1276, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1293 | h1293
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1294 | h1294
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1295 | h1295
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1296 | h1296
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1297 | h1297
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1298 | h1298
                    · linarith only [h1121, h1294, h1298, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1300 | h1300
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1301 | h1301
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1302 | h1302
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1303 | h1303
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1304 | h1304
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1305 | h1305
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1306 | h1306
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1307 | h1307
                                    · linarith only [h0, h1293, h1298, h1307, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                    · linarith only [h0, h1293, h1297, h1298, h1305, h1307, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h0, h1294, h1298, h1306, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                · linarith only [h0, h1293, h1295, h1297, h1298, h1305, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                              · linarith only [h1293, h1297, h1304, h939, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h1296, h1303, h749, hlam]
                          · linarith only [h1295, h1302, h749, hlam]
                        · linarith only [h0, h1294, h1301, hlam]
                      · linarith only [h0, h1293, h1300, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1317 | h1317
                    · linarith only [h1121, h1294, h1317, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1319 | h1319
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1320 | h1320
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1321 | h1321
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1322 | h1322
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1323 | h1323
                              · linarith only [h1295, h1297, h1317, h1319, h1323, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1325 | h1325
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1326 | h1326
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1327 | h1327
                                    · linarith only [h1293, h1323, h1327, h939, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1329 | h1329
                                      · linarith only [h0, h1294, h1317, h1323, h1325, h1327, h1329, h939, hc01, hc23, hlam, hphi, ht12]
                                      · rcases h2bigk with h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [hlam, p1331_0]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h0, hlam, p1331_1]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1121, hlam, p1331_0]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h0, h1317, h1325, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1331_1, u3ehi3]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h0, h1317, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1331_1, u5ehi2]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1317, hc02, hc23, hlam, hphi, p1331_1]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [hlam, p1331_0]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1317, hlam, p1331_0]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1317, h1325, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1331_1, u3ehi3]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1317, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1331_1, u5ehi2]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1293, h1325, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1331_1, u3ehi3]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1331_1]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [hlam, p1331_0]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          rcases p1331_3 (m.d 0 2) (by simp) with h1345 | h1345
                                          · linarith only [h1121, h1345, hlam]
                                          · linarith only [h1293, h1345, hlam]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          rcases p1331_3 (m.d 0 2) (by simp) with h1348 | h1348
                                          · linarith only [h1121, h1348, hlam]
                                          · linarith only [h1294, h1348, hlam]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1293, hlam, p1331_0]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1319, hlam, p1331_0]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1325, hlam, p1331_1]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [hlam, p1331_0]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1327, hlam, p1331_1]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1294, hlam, p1331_0]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1320, hlam, p1331_0]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1326, hlam, p1331_1]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [h1294, h1325, hlam, hphi, ht0b, ht34, ht45, ht5b, p1331_1, u0elo1, u3ehi3]
                                        · have p1331_0 := h1331c.1
                                          have p1331_1 := h1331c.2.1
                                          have p1331_2 := h1331c.2.2.1
                                          have p1331_3 := h1331c.2.2.2
                                          linarith only [hlam, p1331_0]
                                  · linarith only [h0, h1294, h1317, h1326, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                · linarith only [h0, h1294, h1317, h1325, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                            · linarith only [h1121, h1294, h1296, h1322, h749, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
                          · linarith only [h1295, h1296, h1321, h749, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                        · linarith only [h0, h1294, h1320, hlam]
                      · linarith only [h0, h1293, h1319, hlam]
                · linarith only [h1295, h1296, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1121, h1293, h1295, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1369 | h1369
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1370 | h1370
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1371 | h1371
                  · linarith only [h1293, h1294, h1371, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1373 | h1373
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1374 | h1374
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1375 | h1375
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1376 | h1376
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1377 | h1377
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1378 | h1378
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1379 | h1379
                                · linarith only [h1121, h1293, h1373, h1379, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h1121, h1369, h1371, h1376, h1378, h1379, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1382 | h1382
                                · linarith only [h1121, h1293, h1373, h1382, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h1121, h1369, h1382, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1369, h1377, h749, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h1121, h1293, h1369, h1373, h1376, hlam]
                        · linarith only [h1121, h1293, h1369, h1373, h1375, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1121, h1293, h1369, h1373, h1374, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1389 | h1389
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1390 | h1390
                        · linarith only [h1293, h1294, h1369, h1373, h1390, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1392 | h1392
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1393 | h1393
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1394 | h1394
                              · linarith only [h1369, h1371, h1373, h1389, h1394, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1396 | h1396
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1397 | h1397
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1398 | h1398
                                    · linarith only [h1293, h1394, h1398, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · linarith only [h0, h1293, h1390, h1396, h1398, hc45, hlam, hphi, ht34, u3ehi3]
                                  · linarith only [h1370, h1397, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                                · linarith only [h0, h1293, h1369, h1373, h1396, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                            · linarith only [h1370, h1393, h749, hlam]
                          · linarith only [h1369, h1392, h749, hlam]
                      · linarith only [h0, h1293, h1389, hlam]
                · linarith only [h1369, h1370, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1121, h1293, h1369, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1408 | h1408
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1409 | h1409
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1410 | h1410
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1411 | h1411
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1412 | h1412
                    · linarith only [h1121, h1408, h1412, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1414 | h1414
                      · linarith only [h1293, h1408, h1414, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1416 | h1416
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1417 | h1417
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1418 | h1418
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1419 | h1419
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1420 | h1420
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1421 | h1421
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1422 | h1422
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1423 | h1423
                                      · linarith only [h1409, h1423, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                      · linarith only [h1409, h1411, h1423, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                    · linarith only [h1409, h1411, h1414, h1422, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                  · linarith only [h0, h1408, h1414, h1420, h1421, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                · linarith only [h1121, h1408, h1420, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h1293, h1408, h1411, h1419, h939, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
                            · linarith only [h1409, h1418, h749, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h1409, h1417, h749, hlam]
                        · linarith only [h0, h1408, h1416, hlam]
                  · linarith only [h1293, h1408, h1411, hlam]
                · linarith only [h1409, h1410, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1435 | h1435
                · linarith only [h1409, h1435, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1121, h1408, h1435, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1438 | h1438
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1439 | h1439
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1440 | h1440
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1441 | h1441
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1442 | h1442
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1443 | h1443
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1444 | h1444
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1445 | h1445
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1446 | h1446
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1447 | h1447
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1448 | h1448
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1449 | h1449
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1450 | h1450
                                      · linarith only [h1438, h1450, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                      · linarith only [h1121, h1438, h1440, h1441, h1450, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                    · linarith only [h0, h1121, h1293, h1438, h1440, h1441, h1449, hc01, hc12, hlam, hphi]
                                  · linarith only [h1121, h1439, h1448, hlam]
                                · linarith only [h1121, h1439, h1447, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h1293, h1440, h1442, h1446, hlam]
                            · linarith only [h1121, h1439, h1441, h1445, hlam]
                          · linarith only [h1121, h1438, h1441, h1444, hlam]
                        · linarith only [h1121, h1439, h1441, h1443, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h1121, h1439, h1441, h1442, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1461 | h1461
                      · linarith only [h0, h1293, h1441, h1461, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1463 | h1463
                        · linarith only [h0, h1408, h1441, h1463, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1465 | h1465
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1466 | h1466
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1467 | h1467
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1468 | h1468
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1469 | h1469
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1470 | h1470
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1471 | h1471
                                      · linarith only [h1438, h1471, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                      · linarith only [h1438, h1440, h1471, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                    · linarith only [h0, h1293, h1438, h1440, h1470, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                  · linarith only [h1121, h1438, h1469, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h1438, h1441, h1468, h749, hlam]
                              · linarith only [h1440, h1467, h939, hlam]
                            · linarith only [h1439, h1466, h749, hlam]
                          · linarith only [h1438, h1465, h749, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1480 | h1480
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1481 | h1481
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1482 | h1482
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1483 | h1483
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1484 | h1484
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1485 | h1485
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1486 | h1486
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1487 | h1487
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1488 | h1488
                                    · linarith only [h1438, h1440, h1481, h1488, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                    · linarith only [h0, h1293, h1485, h1488, hc01, hc14, hlam, hphi]
                                  · linarith only [h1439, h1487, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                                · linarith only [h1121, h1438, h1439, h1486, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1493 | h1493
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1494 | h1494
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1495 | h1495
                                    · linarith only [h1481, h1485, h1495, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1497 | h1497
                                      · linarith only [h1293, h1438, h1481, h1485, h1497, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                      · rcases h2bigk with h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [hlam, p1499_0]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h0, hlam, p1499_1]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h1121, hlam, p1499_0]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h1293, hlam, p1499_0]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h1408, hlam, p1499_0]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          rcases p1499_3 (m.d 0 2) (by simp) with h1505 | h1505
                                          · linarith only [h0, h1505, hlam]
                                          · rcases p1499_3 (m.d 1 2) (by simp) with h1507 | h1507
                                            · rcases p1499_3 (m.d 2 3) (by simp) with h1508 | h1508
                                              · linarith only [h1480, h1508, hlam]
                                              · linarith only [h1121, h1508, hlam]
                                            · linarith only [h0, h1507, hlam]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [hlam, p1499_0]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h1121, h1439, h1497, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1499_1, u3ehi3]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h0, h1293, hc01, hc12, hlam, hphi, p1499_1]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h0, h1408, hc01, hc12, hlam, hphi, p1499_1]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h0, h1480, hc01, hc12, hlam, hphi, p1499_1]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h1480, hlam, p1499_0]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [hlam, p1499_0]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h0, h1293, h1480, hc01, hc12, hlam, hphi, p1499_1]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h0, h1408, h1480, hc01, hc12, hlam, hphi, p1499_1]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h0, h1481, h1485, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1499_1]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h1481, hlam, p1499_0]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h1493, hlam, p1499_1]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [hlam, p1499_0]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h1495, hlam, p1499_1]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h0, h1482, hc01, hc12, hlam, hphi, p1499_1]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h1482, hlam, p1499_0]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h1494, hlam, p1499_1]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [h0, h1293, h1480, h1494, hc01, hc12, hlam, hphi, p1499_1]
                                        · have p1499_0 := h1499c.1
                                          have p1499_1 := h1499c.2.1
                                          have p1499_2 := h1499c.2.2.1
                                          have p1499_3 := h1499c.2.2.2
                                          linarith only [hlam, p1499_0]
                                  · linarith only [h1121, h1439, h1494, hlam]
                                · linarith only [h1121, h1438, h1439, h1493, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                            · linarith only [h1121, h1439, h1480, h1484, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h1121, h1438, h1480, h1483, hlam]
                        · linarith only [h1121, h1439, h1480, h1482, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h1121, h1438, h1480, h1481, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1537 | h1537
                      · linarith only [h0, h1293, h1480, h1537, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1539 | h1539
                        · linarith only [h0, h1408, h1480, h1539, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1541 | h1541
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1542 | h1542
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1543 | h1543
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1544 | h1544
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1545 | h1545
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1546 | h1546
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1547 | h1547
                                      · linarith only [h1438, h1440, h1547, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                      · rcases h2bigk with h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [hlam, p1549_0]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h0, hlam, p1549_1]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h1121, hlam, p1549_0]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h1293, hlam, p1549_0]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h1408, hlam, p1549_0]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h0, h1539, hc01, hc25, hlam, hphi, ht12, p1549_1]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [hlam, p1549_0]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h1480, hlam, p1549_0]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h1537, hlam, p1549_0]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h1539, hlam, p1549_0]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          rcases p1549_3 (m.d 0 2) (by simp) with h1560 | h1560
                                          · linarith only [h1560, hlam, p1549_0]
                                          · rcases p1549_3 (m.d 1 2) (by simp) with h1562 | h1562
                                            · linarith only [h1480, h1562, hlam]
                                            · linarith only [h0, h1562, hlam]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1549_1]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [hlam, p1549_0]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h1438, h1440, h1537, h1543, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1549_1, u3ehi3]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h0, h1408, hc01, hc23, hlam, hphi, ht12, p1549_1]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          rcases p1549_3 (m.d 0 2) (by simp) with h1569 | h1569
                                          · linarith only [h1569, hlam, p1549_0]
                                          · rcases p1549_3 (m.d 1 2) (by simp) with h1571 | h1571
                                            · linarith only [h1537, h1571, hlam]
                                            · linarith only [h0, h1571, hlam]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1549_1]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h1544, hlam, p1549_1]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [hlam, p1549_0]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h0, h1539, h1544, hc01, hc23, hlam, hphi, ht12, p1549_1]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          rcases p1549_3 (m.d 0 2) (by simp) with h1578 | h1578
                                          · linarith only [h1578, hlam, p1549_0]
                                          · rcases p1549_3 (m.d 1 2) (by simp) with h1580 | h1580
                                            · linarith only [h1539, h1580, hlam]
                                            · linarith only [h0, h1580, hlam]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1549_1]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h1545, hlam, p1549_1]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [h1546, hlam, p1549_0]
                                        · have p1549_0 := h1549c.1
                                          have p1549_1 := h1549c.2.1
                                          have p1549_2 := h1549c.2.2.1
                                          have p1549_3 := h1549c.2.2.2
                                          linarith only [hlam, p1549_0]
                                    · linarith only [h0, h1293, h1541, h1543, h1546, hc01, hc13, hlam, hphi]
                                  · linarith only [h1438, h1480, h1545, h749, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h1438, h1440, h1480, h1541, h1543, h1544, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1590 | h1590
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1591 | h1591
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1592 | h1592
                                    · linarith only [h1543, h1592, h939, hc01, hc24, hlam, hphi, ht12]
                                    · linarith only [h0, h1537, h1592, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                  · linarith only [h1438, h1439, h1480, h1591, h749, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi3]
                                · linarith only [h1438, h1480, h1590, h749, hlam]
                            · linarith only [h1439, h1542, h749, hlam]
                          · linarith only [h1438, h1541, h749, hlam]
                · linarith only [h1438, h1439, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1600 | h1600
                · linarith only [h1438, h1600, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1602 | h1602
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1603 | h1603
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1604 | h1604
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1605 | h1605
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1606 | h1606
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1607 | h1607
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1608 | h1608
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1609 | h1609
                                · linarith only [h1438, h1603, h1609, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                · linarith only [h0, h1121, h1603, h1606, h1609, hc01, hc12, hlam, hphi]
                              · linarith only [h1602, h1606, h1608, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                            · linarith only [h1606, h1607, hc35, hlam, hphi, u3ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1614 | h1614
                            · linarith only [h1606, h1614, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1616 | h1616
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1617 | h1617
                                · linarith only [h1606, h1617, h749, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1619 | h1619
                                  · linarith only [h1603, h1614, h1619, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1621 | h1621
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1622 | h1622
                                      · rcases h2bigk with h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h0, hlam, p1623_1]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h1121, hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h1293, hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h1408, hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          rcases p1623_3 (m.d 0 2) (by simp) with h1629 | h1629
                                          · linarith only [h0, h1629, hlam]
                                          · rcases p1623_3 (m.d 1 2) (by simp) with h1631 | h1631
                                            · rcases p1623_3 (m.d 2 3) (by simp) with h1632 | h1632
                                              · linarith only [h1603, h1632, hlam]
                                              · linarith only [h1121, h1632, hlam]
                                            · linarith only [h0, h1631, hlam]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h0, h1121, hc01, hc12, hlam, hphi, p1623_1]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h0, h1293, hc01, hc12, hlam, hphi, p1623_1]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h0, h1121, h1619, hc01, hc12, hlam, hphi, p1623_1]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h0, h1603, h1614, h1622, hc01, hc34, hlam, hphi, ht12, ht23, p1623_1]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h1603, hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h1617, hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h1619, hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h0, h1604, hc01, hc12, hlam, hphi, p1623_1]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h1604, hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h1604, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1623_1, u3ehi2]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h0, h1121, h1604, h1619, hc01, hc12, hlam, hphi, p1623_1]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h0, h1605, hc01, hc12, hlam, hphi, p1623_1]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h1605, hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h0, h1121, h1605, hc01, hc15, hlam, hphi, p1623_1]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [h1621, hlam, p1623_0]
                                        · have p1623_0 := h1623c.1
                                          have p1623_1 := h1623c.2.1
                                          have p1623_2 := h1623c.2.2.1
                                          have p1623_3 := h1623c.2.2.2
                                          linarith only [hlam, p1623_0]
                                      · linarith only [h1602, h1622, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                                    · linarith only [h1293, h1602, h1621, hlam]
                              · linarith only [h1602, h1616, h939, hlam]
                        · linarith only [h1293, h1602, h1604, h1605, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h1121, h1603, h1604, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1660 | h1660
                      · linarith only [h0, h1293, h1603, h1660, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1662 | h1662
                        · linarith only [h0, h1408, h1603, h1662, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1664 | h1664
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1665 | h1665
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1666 | h1666
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1667 | h1667
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1668 | h1668
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1669 | h1669
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1670 | h1670
                                      · rcases h2bigk with h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [hlam, p1671_0]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h0, hlam, p1671_1]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h1121, hlam, p1671_0]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h1293, hlam, p1671_0]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h1408, hlam, p1671_0]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h0, h1662, h1667, h1669, hc01, hc23, hlam, hphi, ht12, p1671_1]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [hlam, p1671_0]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h1603, hlam, p1671_0]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h1660, hlam, p1671_0]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h1662, hlam, p1671_0]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          rcases p1671_3 (m.d 0 2) (by simp) with h1682 | h1682
                                          · linarith only [h1682, hlam, p1671_0]
                                          · rcases p1671_3 (m.d 1 2) (by simp) with h1684 | h1684
                                            · linarith only [h1603, h1684, hlam]
                                            · linarith only [h0, h1684, hlam]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1671_1]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [hlam, p1671_0]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h0, h1293, hc01, hc23, hlam, hphi, ht12, p1671_1]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h0, h1662, hc01, hc23, hlam, hphi, ht12, p1671_1]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          rcases p1671_3 (m.d 0 2) (by simp) with h1691 | h1691
                                          · linarith only [h1691, hlam, p1671_0]
                                          · rcases p1671_3 (m.d 1 2) (by simp) with h1693 | h1693
                                            · linarith only [h1660, h1693, hlam]
                                            · linarith only [h0, h1693, hlam]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1671_1]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h1667, hlam, p1671_1]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [hlam, p1671_0]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h0, h1662, h1667, hc01, hc23, hlam, hphi, ht12, p1671_1]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          rcases p1671_3 (m.d 0 2) (by simp) with h1700 | h1700
                                          · linarith only [h1700, hlam, p1671_0]
                                          · rcases p1671_3 (m.d 1 2) (by simp) with h1702 | h1702
                                            · linarith only [h1662, h1702, hlam]
                                            · linarith only [h0, h1702, hlam]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1671_1]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h1668, hlam, p1671_1]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [h1669, hlam, p1671_0]
                                        · have p1671_0 := h1671c.1
                                          have p1671_1 := h1671c.2.1
                                          have p1671_2 := h1671c.2.2.1
                                          have p1671_3 := h1671c.2.2.2
                                          linarith only [hlam, p1671_0]
                                      · linarith only [h1602, h1670, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                                    · linarith only [h1293, h1602, h1669, hlam]
                                  · linarith only [h1603, h1664, h1668, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h1603, h1664, h1667, hlam]
                              · linarith only [h1438, h1602, h1603, h1664, h1666, h939, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, u0elo3, u3ehi0]
                            · linarith only [h1438, h1664, h1665, hc35, hlam, hphi, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1715 | h1715
                            · linarith only [h1664, h1715, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1717 | h1717
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1718 | h1718
                                · linarith only [h1664, h1718, h749, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h1603, h1718, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h1602, h1717, h939, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1722 | h1722
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1723 | h1723
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1724 | h1724
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1725 | h1725
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1726 | h1726
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1727 | h1727
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1728 | h1728
                                · linarith only [h1438, h1722, h1728, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                · linarith only [h0, h1121, h1722, h1725, h1728, hc01, hc12, hlam, hphi]
                              · linarith only [h1438, h1725, h1727, hc45, hlam, hphi, ht34, u3ehi0]
                            · linarith only [h1438, h1725, h1726, hc35, hlam, hphi, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1733 | h1733
                            · linarith only [h1725, h1733, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1735 | h1735
                              · linarith only [h1438, h1602, h1725, h1735, hc34, hlam, hphi, u3ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1737 | h1737
                                · linarith only [h1722, h1725, h1735, h1737, hc45, hlam, hphi, ht34, u3ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1739 | h1739
                                  · linarith only [h1722, h1733, h1739, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1741 | h1741
                                    · linarith only [h0, h1121, h1722, h1725, h1735, h1741, hc01, hc24, hlam, hphi, ht12]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1743 | h1743
                                      · linarith only [h0, h1121, h1722, h1725, h1735, h1743, hc01, hc34, hlam, hphi, ht12, ht23]
                                      · linarith only [h1438, h1743, hc45, hlam, hphi, ht34, u3ehi0]
                        · linarith only [h0, h1121, h1722, h1724, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1121, h1722, h1723, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1748 | h1748
                      · linarith only [h0, h1293, h1722, h1748, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1750 | h1750
                        · linarith only [h0, h1408, h1722, h1750, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1752 | h1752
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1753 | h1753
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1754 | h1754
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1755 | h1755
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1756 | h1756
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1757 | h1757
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1758 | h1758
                                      · linarith only [h1438, h1602, h1758, hc34, hlam, hphi, u3ehi0]
                                      · linarith only [h1438, h1752, h1754, h1758, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                    · linarith only [h0, h1293, h1722, h1752, h1754, h1757, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h0, h1722, h1756, hc01, hc35, hlam, hphi, ht12, ht23]
                                · linarith only [h1722, h1752, h1755, hlam]
                              · linarith only [h1438, h1752, h1754, hc45, hlam, hphi, ht34, u3ehi0]
                            · linarith only [h1438, h1752, h1753, hc35, hlam, hphi, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1766 | h1766
                            · linarith only [h1752, h1766, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1768 | h1768
                              · linarith only [h1438, h1602, h1752, h1768, hc34, hlam, hphi, u3ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1770 | h1770
                                · linarith only [h0, h1722, h1752, h1770, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h1722, h1770, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 3546000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_R_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_0_L_I_L_R_M_IR_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_0_L_I_L_R_M_IR_x1 m hb0 hb2 hb3 hb5 h0

set_option maxHeartbeats 3494000 in
set_option maxHeartbeats 3494000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_R_M_IR_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                                · linarith only [h0, h10, h16, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h0, h10, h13, h16, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                                · linarith only [h0, h10, h19, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h0, h10, h13, h19, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h0, h13, h14, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                            · linarith only [h0, h13, h23, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                                · linarith only [h0, h10, h13, h26, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                                  · linarith only [h0, h10, h23, h28, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                                    · linarith only [h0, h11, h30, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h2, h25, h30, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                                · linarith only [h0, h10, h13, h25, h33, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                                  · linarith only [h0, h10, h23, h35, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                                    · linarith only [h11, h25, h37, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                                      · linarith only [h11, h25, h39, hc34, hlam, hphi, ht23, u2ehi3]
                                      · linarith only [h0, h10, h13, h39, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h11, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                      · linarith only [h10, h44, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                        · linarith only [h0, h10, h4, h46, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                                      · linarith only [h1, h48, h54, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h2, h50, h54, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                    · linarith only [h44, h50, h53, hlam]
                                  · linarith only [h10, h49, h52, hlam]
                                · linarith only [h0, h10, h4, h49, h51, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                                    · linarith only [h44, h50, h62, hc24, hlam, hphi, u2ehi1]
                                    · linarith only [h0, h4, h44, h62, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h0, h10, h4, h61, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h10, h48, h60, hlam]
                            · linarith only [h0, h4, h48, h49, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                            · linarith only [h0, h4, h48, h68, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                                · linarith only [h0, h10, h4, h48, h71, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h10, h4, h7, h71, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                                · linarith only [h10, h48, h74, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h10, h4, h7, h74, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                              · linarith only [h2, h82, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                                · linarith only [h0, h77, h84, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h1, h80, h84, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h0, h4, h8, h80, h81, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h7, h77, h80, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h6, h77, h79, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h77, h78, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
                      · linarith only [h77, h91, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h5, h9, h91, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h94 | h94
                  · linarith only [h7, h8, h94, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h98 | h98
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                            · linarith only [h1, h100, h8, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                              · linarith only [h102, h2, h94, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                                · linarith only [h0, h104, h96, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h1, h104, h8, h99, hc23, hc35, hlam, hphi]
                          · linarith only [h7, h8, h99, hc13, hc35, hlam, hphi]
                        · linarith only [h0, h6, h96, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h96, h97, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h4, h8, h96, hc35, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h111 | h111
                · rcases m.htr 0 4 5 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
                          · linarith only [h1, h116, h7, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                                · linarith only [h0, h1, h113, h118, h120, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                                  · linarith only [h0, h114, h120, h122, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · linarith only [h1, h118, h122, h7, hc23, hc34, hlam, hphi]
                              · linarith only [h112, h114, h119, h7, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h111, h118, h7, hc13, hc34, hlam, hphi]
                        · linarith only [h111, h115, h6, h7, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h113, h114, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h113, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h111, h112, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h131 | h131
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h132 | h132
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h135 | h135
                          · linarith only [h1, h135, h7, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
                            · linarith only [h1, h111, h137, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                                · linarith only [h140, h4, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                                  · linarith only [h1, h111, h132, h142, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                                    · linarith only [h0, h133, h144, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h131, h144, h7, hc34, hlam, hphi, ht23, u2ehi3]
                              · linarith only [h131, h133, h139, h7, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h132, h134, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h132, h133, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h132, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h154 | h154
                          · linarith only [h1, h131, h154, h7, hc45, hlam, hphi, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h156 | h156
                            · linarith only [h1, h111, h156, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                              · linarith only [h131, h158, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
                                · linarith only [h1, h151, h160, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h162 | h162
                                  · linarith only [h1, h111, h151, h162, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h164 | h164
                                    · linarith only [h1, h131, h151, h152, h164, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h166 | h166
                                      · linarith only [h1, h131, h151, h166, h7, hc34, hlam, hphi, ht23, u2ehi2]
                                      · linarith only [h1, h151, h166, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h151, h153, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h151, h152, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h151, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
          · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h174 | h174
          · linarith only [h174, h4, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h176 | h176
            · linarith only [h176, h4, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
              · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
                · rcases m.htr 0 4 5 (by decide) (by decide) with h180 | h180
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h181 | h181
                    · linarith only [h0, h181, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h183 | h183
                      · linarith only [h0, h174, h183, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
                        · linarith only [h0, h176, h185, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h188 | h188
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h191 | h191
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h192 | h192
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h193 | h193
                                      · linarith only [h1, h187, h193, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h189, h193, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                    · linarith only [h174, h189, h192, h2, hlam]
                                  · linarith only [h0, h191, h4, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h0, h190, h4, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h178, h180, h183, h189, h4, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h179, h181, h188, h4, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h178, h181, h187, h4, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
                    · linarith only [h0, h174, h180, h202, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h204 | h204
                      · linarith only [h0, h174, h180, h204, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h206 | h206
                        · linarith only [h0, h174, h180, h206, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h208 | h208
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h209 | h209
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h210 | h210
                              · linarith only [h174, h180, h2, h210, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h213 | h213
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h214 | h214
                                    · linarith only [h0, h174, h180, h212, h214, hc23, hlam, hphi, u2ehi1]
                                    · linarith only [h0, h174, h214, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                  · linarith only [h1, h209, h213, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h0, h212, h4, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h179, h208, h209, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h178, h202, h208, h4, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h221 | h221
                  · linarith only [h178, h179, h221, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h223 | h223
                    · linarith only [h0, h174, h223, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
                      · linarith only [h0, h174, h225, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h227 | h227
                        · linarith only [h0, h176, h227, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h230 | h230
                            · linarith only [h1, h179, h230, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h232 | h232
                              · linarith only [h2, h221, h232, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h235 | h235
                                  · linarith only [h1, h179, h229, h235, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                  · linarith only [h235, h4, hc35, hlam, hphi, ht23, u2ehi0]
                                · linarith only [h0, h1, h229, h234, h4, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · linarith only [h178, h179, h229, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h240 | h240
                · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
                    · linarith only [h0, h174, h242, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
                      · linarith only [h0, h176, h178, h240, h244, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h246 | h246
                        · linarith only [h0, h176, h178, h240, h246, hc34, hlam, hphi, ht23, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h248 | h248
                          · linarith only [h1, h178, h248, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h250 | h250
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h251 | h251
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h252 | h252
                                · linarith only [h176, h178, h240, h252, hc23, hlam, hphi, u2ehi0]
                                · linarith only [h0, h252, h4, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h241, h248, h250, h251, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h178, h240, h250, hc13, hc34, hlam, hphi]
                  · linarith only [h178, h240, h241, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h258 | h258
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h259 | h259
                    · linarith only [h0, h176, h259, hc25, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h261 | h261
                      · linarith only [h0, h261, h4, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h263 | h263
                        · linarith only [h0, h240, h263, h4, hc35, hlam, hphi, ht23, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h265 | h265
                          · linarith only [h1, h178, h2, h240, h261, h265, hc35, hlam, hphi, ht23, u2ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h267 | h267
                            · linarith only [h1, h240, h267, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h270 | h270
                                · linarith only [h0, h178, h270, h4, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h270, h4, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h178, h258, h261, h269, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h274 | h274
                    · linarith only [h0, h274, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h276 | h276
                      · linarith only [h0, h276, h4, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h278 | h278
                        · linarith only [h0, h178, h258, h278, h4, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h280 | h280
                          · linarith only [h1, h178, h258, h280, hc45, hlam, hphi, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h282 | h282
                            · linarith only [h1, h240, h282, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h284 | h284
                              · linarith only [h178, h2, h258, h284, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h286 | h286
                                · linarith only [h0, h178, h286, h4, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h286, h4, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h289 | h289
        · rcases m.htr 0 2 4 (by decide) (by decide) with h290 | h290
          · rcases m.htr 0 2 5 (by decide) (by decide) with h291 | h291
            · linarith only [h0, h291, h3, hlam]
            · linarith only [h290, h291, hc25, hlam, hphi, u2ehi3]
          · linarith only [h289, h290, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h295 | h295
          · linarith only [h289, h295, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h297 | h297
            · linarith only [h289, h297, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h299 | h299
              · rcases m.htr 0 3 5 (by decide) (by decide) with h300 | h300
                · linarith only [h1, h3, h300, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h302 | h302
                  · linarith only [h0, h299, h3, h300, h302, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h304 | h304
                    · linarith only [h0, h295, h299, h300, h304, hc35, hlam, hphi, ht23, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h306 | h306
                      · linarith only [h0, h295, h306, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h308 | h308
                        · linarith only [h1, h297, h3, h304, h308, hlam]
                        · linarith only [h1, h3, h304, h308, hc25, hlam, hphi, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h311 | h311
                · linarith only [h0, h299, h3, h311, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h313 | h313
                  · linarith only [h2, h3, h313, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h315 | h315
                    · linarith only [h0, h289, h315, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h317 | h317
                      · linarith only [h0, h295, h317, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h319 | h319
                        · linarith only [h1, h3, h315, h319, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · linarith only [h1, h3, h315, h319, hc25, hlam, hphi, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h322 | h322
      · rcases m.htr 0 2 3 (by decide) (by decide) with h323 | h323
        · rcases m.htr 0 2 4 (by decide) (by decide) with h324 | h324
          · linarith only [h0, h2, h324, hlam]
          · linarith only [h323, h324, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h327 | h327
          · linarith only [h323, h327, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h329 | h329
            · linarith only [h323, h329, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h331 | h331
              · linarith only [h1, h2, h331, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h333 | h333
                · rcases m.htr 0 4 5 (by decide) (by decide) with h334 | h334
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h335 | h335
                    · linarith only [h0, h2, h335, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h337 | h337
                      · linarith only [h0, h2, h327, h337, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h0, h2, h337, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h334, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h341 | h341
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h342 | h342
                    · linarith only [h0, h323, h342, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h344 | h344
                      · linarith only [h1, h2, h342, h344, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h1, h2, h342, h344, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h341, hc45, hlam, hphi, ht23, ht34, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h348 | h348
        · rcases m.htr 0 2 4 (by decide) (by decide) with h349 | h349
          · linarith only [h0, h2, h349, hlam]
          · linarith only [h348, h349, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h352 | h352
          · linarith only [h348, h352, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h354 | h354
            · linarith only [h348, h354, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h356 | h356
              · linarith only [h1, h2, h356, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h358 | h358
                · linarith only [h0, h322, h356, h358, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h360 | h360
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h361 | h361
                    · linarith only [h0, h2, h361, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h363 | h363
                      · linarith only [h1, h322, h352, h360, h361, h363, hlam]
                      · linarith only [h1, h2, h361, h363, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h360, hc45, hlam, hphi, ht23, ht34, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h367 | h367
    · rcases m.htr 0 1 5 (by decide) (by decide) with h368 | h368
      · rcases m.htr 0 2 3 (by decide) (by decide) with h369 | h369
        · linarith only [h0, h1, h369, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h371 | h371
          · linarith only [h369, h371, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h373 | h373
            · linarith only [h369, h373, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h375 | h375
              · rcases m.htr 0 3 5 (by decide) (by decide) with h376 | h376
                · rcases m.htr 0 4 5 (by decide) (by decide) with h377 | h377
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h378 | h378
                    · linarith only [h0, h369, h378, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h378, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h381 | h381
                    · linarith only [h0, h1, h381, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h381, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h376, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h375, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h386 | h386
        · linarith only [h0, h1, h386, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h388 | h388
          · linarith only [h386, h388, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h390 | h390
            · linarith only [h386, h390, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h392 | h392
              · rcases m.htr 0 3 5 (by decide) (by decide) with h393 | h393
                · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
                  · linarith only [h367, h368, h394, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h396 | h396
                    · linarith only [h0, h1, h386, h393, h396, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h0, h1, h396, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h393, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h392, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h401 | h401
      · rcases m.htr 0 2 3 (by decide) (by decide) with h402 | h402
        · linarith only [h0, h1, h402, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h404 | h404
          · linarith only [h402, h404, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h406 | h406
            · linarith only [h402, h406, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h408 | h408
              · rcases m.htr 0 3 5 (by decide) (by decide) with h409 | h409
                · rcases m.htr 0 4 5 (by decide) (by decide) with h410 | h410
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h411 | h411
                    · linarith only [h0, h1, h402, h411, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h411, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h367, h410, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h367, h408, h409, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h408, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h417 | h417
        · linarith only [h0, h1, h417, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h419 | h419
          · linarith only [h417, h419, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h421 | h421
            · linarith only [h417, h421, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h423 | h423
              · rcases m.htr 0 3 5 (by decide) (by decide) with h424 | h424
                · rcases m.htr 0 4 5 (by decide) (by decide) with h425 | h425
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h426 | h426
                    · linarith only [h0, h1, h417, h426, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h426, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h367, h425, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h367, h423, h424, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h423, hc34, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 3494000 in
set_option maxHeartbeats 3494000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_R_M_IR_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h432 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h433 | h433
  · rcases m.htr 0 1 5 (by decide) (by decide) with h434 | h434
    · rcases m.htr 0 2 3 (by decide) (by decide) with h435 | h435
      · rcases m.htr 0 2 4 (by decide) (by decide) with h436 | h436
        · rcases m.htr 0 2 5 (by decide) (by decide) with h437 | h437
          · rcases m.htr 0 3 4 (by decide) (by decide) with h438 | h438
            · rcases m.htr 0 3 5 (by decide) (by decide) with h439 | h439
              · rcases m.htr 0 4 5 (by decide) (by decide) with h440 | h440
                · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h442 | h442
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h443 | h443
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
                        · linarith only [h0, h432, h444, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h432, h438, h441, h444, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h433, h443, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h433, h442, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h432, h435, h438, h440, h441, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h451 | h451
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h452 | h452
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h453 | h453
                        · linarith only [h0, h432, h453, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h432, h438, h450, h453, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h433, h452, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h432, h450, h451, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h434, h450, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h459 | h459
                · linarith only [h438, h439, h459, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h461 | h461
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h462 | h462
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h463 | h463
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h464 | h464
                        · linarith only [h0, h432, h464, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h438, h439, h461, h464, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h433, h462, h463, hc25, hlam, hphi, u2ehi3]
                    · linarith only [h0, h433, h462, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h434, h461, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h470 | h470
              · rcases m.htr 0 4 5 (by decide) (by decide) with h471 | h471
                · rcases m.htr 1 2 3 (by decide) (by decide) with h472 | h472
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h473 | h473
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h474 | h474
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h475 | h475
                        · linarith only [h432, h438, h470, h475, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h477 | h477
                          · linarith only [h0, h433, h475, h477, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h438, h470, h472, h477, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h433, h474, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h432, h472, h473, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h434, h472, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h438, h470, h471, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h484 | h484
                · rcases m.htr 1 2 3 (by decide) (by decide) with h485 | h485
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h486 | h486
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h487 | h487
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
                        · linarith only [h0, h432, h488, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h490 | h490
                          · linarith only [h432, h470, h490, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h492 | h492
                            · linarith only [h0, h433, h492, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h433, h484, h485, h488, h492, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h432, h485, h487, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h433, h486, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h433, h484, h485, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h498 | h498
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h499 | h499
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h500 | h500
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h501 | h501
                        · linarith only [h0, h432, h438, h501, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h503 | h503
                          · linarith only [h432, h470, h503, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h505 | h505
                            · linarith only [h433, h484, h505, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h507 | h507
                              · linarith only [h432, h438, h498, h507, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h509 | h509
                                · linarith only [h0, h434, h470, h498, h501, h505, h509, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h511 | h511
                                  · linarith only [h433, h484, h498, h501, h511, hc24, hlam, hphi, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h513 | h513
                                    · linarith only [h433, h484, h498, h501, h513, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h432, h438, h498, h513, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h434, h500, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h432, h498, h499, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h433, h498, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h435, h437, hc25, hlam, hphi, u2ehi2]
        · linarith only [h435, h436, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h432, h435, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h522 | h522
      · rcases m.htr 0 2 4 (by decide) (by decide) with h523 | h523
        · rcases m.htr 0 2 5 (by decide) (by decide) with h524 | h524
          · rcases m.htr 0 3 4 (by decide) (by decide) with h525 | h525
            · rcases m.htr 0 3 5 (by decide) (by decide) with h526 | h526
              · linarith only [h432, h434, h526, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h528 | h528
                · linarith only [h432, h434, h525, h528, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h530 | h530
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h531 | h531
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h532 | h532
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h533 | h533
                        · linarith only [h432, h434, h533, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h525, h526, h533, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h433, h524, h532, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h432, h530, h531, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h432, h525, h530, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h539 | h539
              · linarith only [h433, h434, h525, h539, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h541 | h541
                · linarith only [h433, h434, h541, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h543 | h543
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h544 | h544
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h545 | h545
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h546 | h546
                        · linarith only [h432, h525, h546, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h548 | h548
                          · linarith only [h433, h434, h539, h546, h548, hlam]
                          · linarith only [h433, h434, h543, h546, h548, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h433, h545, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h432, h543, h544, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h524, h543, hc23, hlam, hphi, u2ehi4]
          · linarith only [h522, h524, hc25, hlam, hphi, u2ehi2]
        · linarith only [h522, h523, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h432, h522, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h557 | h557
    · rcases m.htr 0 2 3 (by decide) (by decide) with h558 | h558
      · rcases m.htr 0 2 4 (by decide) (by decide) with h559 | h559
        · rcases m.htr 0 2 5 (by decide) (by decide) with h560 | h560
          · rcases m.htr 0 3 4 (by decide) (by decide) with h561 | h561
            · linarith only [h432, h433, h561, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h563 | h563
              · rcases m.htr 0 4 5 (by decide) (by decide) with h564 | h564
                · rcases m.htr 1 2 3 (by decide) (by decide) with h565 | h565
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h566 | h566
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h567 | h567
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h568 | h568
                        · linarith only [h561, h563, h568, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h433, h557, h567, h568, hc34, hlam, hphi, ht23, u2ehi4]
                      · linarith only [h433, h557, h566, h567, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h559, h566, hlam]
                  · linarith only [h0, h559, h565, hc23, hlam, hphi, u2ehi3]
                · linarith only [h433, h557, h564, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h575 | h575
                · rcases m.htr 1 2 3 (by decide) (by decide) with h576 | h576
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h577 | h577
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h578 | h578
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h579 | h579
                        · linarith only [h432, h433, h577, h579, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h433, h557, h578, h579, hc34, hlam, hphi, ht23, u2ehi4]
                      · linarith only [h433, h557, h577, h578, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h432, h576, h577, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h559, h576, hc23, hlam, hphi, u2ehi3]
                · linarith only [h433, h557, h575, hlam]
          · linarith only [h559, h560, hc25, hlam, hphi, u2ehi3]
        · linarith only [h558, h559, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h432, h558, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h589 | h589
      · rcases m.htr 0 2 4 (by decide) (by decide) with h590 | h590
        · rcases m.htr 0 2 5 (by decide) (by decide) with h591 | h591
          · rcases m.htr 0 3 4 (by decide) (by decide) with h592 | h592
            · linarith only [h432, h433, h592, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h594 | h594
              · linarith only [h432, h557, h594, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h596 | h596
                · rcases m.htr 1 2 3 (by decide) (by decide) with h597 | h597
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h598 | h598
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h599 | h599
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h600 | h600
                        · linarith only [h432, h433, h592, h598, h600, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h432, h433, h597, h600, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h432, h433, h591, h597, h598, h599, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h432, h590, h597, h598, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h590, h597, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
                  · linarith only [h432, h433, h596, h606, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h591, h606, hc23, hlam, hphi, u2ehi4]
          · linarith only [h589, h591, hc25, hlam, hphi, u2ehi2]
        · linarith only [h589, h590, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h432, h589, hlam]

end R2N4
