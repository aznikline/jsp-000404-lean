import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_62S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3190000 in
set_option maxHeartbeats 3190000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h768 | h768
  · rcases m.htr 0 1 4 (by decide) (by decide) with h769 | h769
    · linarith only [h0, h769, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h771 | h771
      · rcases m.htr 0 2 3 (by decide) (by decide) with h772 | h772
        · rcases m.htr 0 2 4 (by decide) (by decide) with h773 | h773
          · rcases m.htr 0 2 5 (by decide) (by decide) with h774 | h774
            · rcases m.htr 0 3 4 (by decide) (by decide) with h775 | h775
              · linarith only [h0, h768, h775, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h777 | h777
                · rcases m.htr 0 4 5 (by decide) (by decide) with h778 | h778
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h779 | h779
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h780 | h780
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h781 | h781
                        · linarith only [h0, h768, h775, h781, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h783 | h783
                          · linarith only [h0, h771, h783, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                          · linarith only [h769, h773, h778, h783, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h774, h780, hlam]
                    · linarith only [h0, h772, h779, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h768, h769, h777, h778, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h789 | h789
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h790 | h790
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h791 | h791
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h792 | h792
                        · linarith only [h768, h775, h789, h792, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h794 | h794
                          · linarith only [h769, h771, h794, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi4]
                          · linarith only [h769, h789, h794, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h774, h791, hlam]
                    · linarith only [h0, h772, h790, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h769, h771, h789, hlam]
            · linarith only [h0, h771, h774, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h801 | h801
            · rcases m.htr 0 3 4 (by decide) (by decide) with h802 | h802
              · linarith only [h0, h768, h802, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h804 | h804
                · rcases m.htr 0 4 5 (by decide) (by decide) with h805 | h805
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h806 | h806
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h807 | h807
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h808 | h808
                        · linarith only [h0, h768, h802, h808, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h810 | h810
                          · linarith only [h0, h771, h810, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                          · linarith only [h805, h810, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                      · linarith only [h0, h801, h807, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h772, h806, hlam]
                  · linarith only [h0, h768, h773, h804, h805, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h816 | h816
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h817 | h817
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h818 | h818
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h819 | h819
                        · linarith only [h768, h802, h816, h819, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h821 | h821
                          · linarith only [h0, h771, h821, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                          · linarith only [h816, h821, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                      · linarith only [h0, h768, h801, h817, h818, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h772, h817, hlam]
                  · linarith only [h0, h771, h773, h816, hlam]
            · linarith only [h0, h771, h801, hlam]
        · linarith only [h0, h768, h772, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h829 | h829
        · rcases m.htr 0 2 4 (by decide) (by decide) with h830 | h830
          · rcases m.htr 0 2 5 (by decide) (by decide) with h831 | h831
            · rcases m.htr 0 3 4 (by decide) (by decide) with h832 | h832
              · linarith only [h0, h768, h832, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h834 | h834
                · linarith only [h768, h771, h834, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h836 | h836
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h837 | h837
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h839 | h839
                        · linarith only [h768, h771, h832, h838, h839, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h841 | h841
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h842 | h842
                            · linarith only [h771, h837, h839, h841, h842, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h844 | h844
                              · linarith only [h768, h834, h837, h844, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h846 | h846
                                · linarith only [h830, h846, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                · linarith only [h836, h846, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                          · linarith only [h0, h830, h836, h841, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                      · linarith only [h0, h831, h838, hlam]
                    · linarith only [h0, h829, h837, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h852 | h852
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h853 | h853
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h854 | h854
                        · linarith only [h768, h771, h832, h853, h854, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h856 | h856
                          · linarith only [h769, h836, h856, hc01, hlam, hphi, u1elo3]
                          · linarith only [h768, h769, h852, h856, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h831, h853, hlam]
                    · linarith only [h0, h829, h852, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h861 | h861
              · linarith only [h0, h768, h861, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h863 | h863
                · linarith only [h0, h768, h831, h863, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h865 | h865
                  · linarith only [h830, h831, h865, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h867 | h867
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h868 | h868
                      · linarith only [h830, h831, h868, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h870 | h870
                        · linarith only [h0, h768, h861, h868, h870, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h872 | h872
                          · linarith only [h865, h872, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · linarith only [h768, h769, h867, h872, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h829, h867, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h876 | h876
            · rcases m.htr 0 3 4 (by decide) (by decide) with h877 | h877
              · linarith only [h0, h768, h877, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h879 | h879
                · linarith only [h768, h771, h879, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h881 | h881
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h882 | h882
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h883 | h883
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h884 | h884
                        · linarith only [h768, h771, h830, h877, h883, h884, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h886 | h886
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h887 | h887
                            · linarith only [h768, h771, h882, h884, h886, h887, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h889 | h889
                              · linarith only [h768, h771, h879, h882, h883, h889, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h891 | h891
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h892 | h892
                                  · rcases h0bigk with h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [hlam, p893_0]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h0, hlam, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h771, h830, h876, h883, h887, h891, hc03, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p893_1, u1elo1, u4ehi4]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h769, hlam, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h771, hlam, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h830, h887, hc01, hc34, hlam, hphi, ht12, ht23, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [hlam, p893_0]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h768, h830, h882, h887, hc23, hc34, hlam, hphi, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h830, hlam, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h768, h771, h830, h882, h887, hc23, hc34, hlam, hphi, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h768, hlam, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h829, hlam, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [hlam, p893_0]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h877, hlam, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h879, hlam, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h768, h830, h876, h882, h887, h891, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p893_1, u0elo3, u4ehi4]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h769, h876, h891, hlam, hphi, ht01, ht0b, ht45, ht5b, p893_1, u1elo3, u4ehi4]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      rcases p893_3 (m.d 0 1) (by simp) with h911 | h911
                                      · linarith only [h769, h911, hlam]
                                      · linarith only [h768, h911, hlam]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [hlam, p893_0]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h768, h769, h771, h830, h876, h882, h887, h891, hc23, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p893_1, u1elo3, u4ehi4]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h768, h830, h876, h882, h887, h891, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p893_1, u0elo4, u4ehi4]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h876, hlam, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h768, h830, h876, h882, h887, hc23, hc34, hlam, hphi, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [h881, hlam, p893_1]
                                    · have p893_0 := h893c.1
                                      have p893_1 := h893c.2.1
                                      have p893_2 := h893c.2.2.1
                                      have p893_3 := h893c.2.2.2
                                      linarith only [hlam, p893_0]
                                  · linarith only [h830, h876, h887, h891, h892, hlam]
                                · linarith only [h0, h768, h830, h882, h891, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h769, h881, h886, hlam]
                      · linarith only [h0, h876, h883, hlam]
                    · linarith only [h0, h829, h882, hlam]
                  · linarith only [h830, h876, h881, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h927 | h927
              · linarith only [h0, h768, h927, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h929 | h929
                · linarith only [h0, h768, h876, h929, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h931 | h931
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h932 | h932
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h933 | h933
                      · linarith only [h0, h876, h933, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h935 | h935
                        · linarith only [h768, h927, h935, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h937 | h937
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h938 | h938
                            · linarith only [h768, h932, h935, h938, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h940 | h940
                              · linarith only [h0, h768, h929, h932, h933, h937, h940, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                              · linarith only [h0, h768, h932, h933, h940, hc23, hc35, hlam, hphi]
                          · linarith only [h931, h937, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · linarith only [h0, h829, h932, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h945 | h945
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h946 | h946
                      · linarith only [h0, h768, h876, h945, h946, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h948 | h948
                        · linarith only [h768, h927, h948, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h950 | h950
                          · linarith only [h931, h950, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · linarith only [h768, h769, h945, h950, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h829, h945, hlam]
        · linarith only [h0, h768, h829, hlam]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h955 | h955
    · linarith only [h0, h955, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h957 | h957
      · rcases m.htr 0 2 3 (by decide) (by decide) with h958 | h958
        · rcases m.htr 0 2 4 (by decide) (by decide) with h959 | h959
          · rcases m.htr 0 2 5 (by decide) (by decide) with h960 | h960
            · rcases m.htr 0 3 4 (by decide) (by decide) with h961 | h961
              · rcases m.htr 0 3 5 (by decide) (by decide) with h962 | h962
                · rcases m.htr 0 4 5 (by decide) (by decide) with h963 | h963
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h964 | h964
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h965 | h965
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h966 | h966
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h967 | h967
                          · linarith only [h955, h957, h964, h966, h967, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                          · linarith only [h955, h958, h961, h963, h967, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h768, h961, h966, hlam]
                      · linarith only [h0, h960, h965, hlam]
                    · linarith only [h0, h958, h964, hlam]
                  · linarith only [h955, h957, h963, hlam]
                · linarith only [h768, h957, h962, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h975 | h975
                · rcases m.htr 0 4 5 (by decide) (by decide) with h976 | h976
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h977 | h977
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h978 | h978
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h979 | h979
                        · linarith only [h961, h975, h979, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h981 | h981
                          · linarith only [h768, h957, h979, h981, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h768, h959, h976, h979, h981, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h960, h978, hlam]
                    · linarith only [h0, h957, h958, h976, h977, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                  · linarith only [h768, h957, h961, h976, hlam]
                · linarith only [h768, h957, h975, hlam]
            · linarith only [h0, h957, h959, h960, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h989 | h989
            · rcases m.htr 0 3 4 (by decide) (by decide) with h990 | h990
              · linarith only [h958, h959, h990, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h992 | h992
                · rcases m.htr 0 4 5 (by decide) (by decide) with h993 | h993
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h994 | h994
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h995 | h995
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h996 | h996
                        · linarith only [h990, h992, h994, h996, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h998 | h998
                          · linarith only [h768, h957, h996, h998, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h768, h993, h996, h998, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h957, h989, h993, h995, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                    · linarith only [h0, h957, h958, h993, h994, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                  · linarith only [h0, h957, h959, h993, hlam]
                · linarith only [h768, h957, h992, hlam]
            · linarith only [h0, h957, h989, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1006 | h1006
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1007 | h1007
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1008 | h1008
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1009 | h1009
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1010 | h1010
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1011 | h1011
                    · linarith only [h1006, h1010, h1011, h958, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1013 | h1013
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1014 | h1014
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1015 | h1015
                          · linarith only [h0, h1011, h1015, h957, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h1006, h1010, h1015, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                        · linarith only [h1008, h1014, h768, hlam]
                      · linarith only [h0, h1007, h1013, hlam]
                  · linarith only [h1010, h955, h957, hlam]
                · linarith only [h0, h1008, h1009, h957, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
              · linarith only [h1006, h1008, h958, hlam]
            · linarith only [h0, h1006, h1007, h957, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1024 | h1024
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1025 | h1025
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1026 | h1026
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1027 | h1027
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1028 | h1028
                    · linarith only [h1024, h1028, h958, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1030 | h1030
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1031 | h1031
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1032 | h1032
                          · linarith only [h0, h1028, h1032, h957, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h1027, h1032, h955, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h1025, h1031, h768, hlam]
                      · linarith only [h0, h1024, h1027, h1030, h957, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                  · linarith only [h1027, h955, h957, hlam]
                · linarith only [h0, h1025, h1026, h957, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1039 | h1039
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1040 | h1040
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1041 | h1041
                    · linarith only [h1024, h1041, h958, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1043 | h1043
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1044 | h1044
                        · linarith only [h1025, h1044, h768, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1046 | h1046
                          · linarith only [h0, h1041, h1044, h1046, h957, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h1040, h1046, h955, h957, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                      · linarith only [h0, h1024, h1043, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1025, h1040, h957, h958, hlam]
                · linarith only [h0, h1039, h957, h958, hlam]
            · linarith only [h0, h1024, h957, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1053 | h1053
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1054 | h1054
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1055 | h1055
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1056 | h1056
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1057 | h1057
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1058 | h1058
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1059 | h1059
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1060 | h1060
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1061 | h1061
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1062 | h1062
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1063 | h1063
                            · linarith only [h1053, h1063, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1065 | h1065
                              · linarith only [h1056, h1063, h1065, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1067 | h1067
                                · linarith only [h0, h1054, h1067, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                                · linarith only [h1058, h1067, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                          · linarith only [h1058, h1062, h955, hlam]
                        · linarith only [h1056, h1061, h768, hlam]
                      · linarith only [h0, h1055, h1060, hlam]
                    · linarith only [h0, h1053, h1059, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1074 | h1074
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1075 | h1075
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1076 | h1076
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1077 | h1077
                          · linarith only [h1058, h1076, h1077, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1079 | h1079
                            · linarith only [h1053, h1079, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1081 | h1081
                              · linarith only [h1056, h1074, h1079, h1081, h768, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1083 | h1083
                                · linarith only [h1077, h1083, h955, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1085 | h1085
                                  · linarith only [h1056, h1077, h1085, h955, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                  · rcases h0bigk with h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [hlam, p1087_0]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h0, hlam, p1087_1]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h768, hlam, p1087_0]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h955, hlam, p1087_1]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h957, hlam, p1087_1]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p1087_1, u1elo1]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [hlam, p1087_0]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h0, h1057, h1081, h1083, hlam, hphi, ht01, ht0b, ht45, ht5b, p1087_1, u1elo1, u4ehi2]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, p1087_1, u1elo1, u4ehi0]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h0, h957, hc01, hlam, hphi, p1087_1, u1elo1]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h768, hc01, hlam, hphi, p1087_1, u1elo2]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h1053, hlam, p1087_1]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [hlam, p1087_0]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h0, h1053, h1054, hlam, hphi, ht01, ht0b, ht45, ht5b, p1087_1, u1elo1, u4ehi2]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h0, h1053, h1055, h1083, hlam, hphi, ht01, ht0b, ht45, ht5b, p1087_1, u1elo1, u4ehi2]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h1077, h955, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1087_1]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h1054, hlam, p1087_0]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h1056, hlam, p1087_0]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [hlam, p1087_0]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h1058, hlam, p1087_0]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h1075, h957, hc01, hlam, hphi, p1087_1, u1elo1]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h1055, hlam, p1087_1]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h1057, hlam, p1087_0]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [h0, h1053, h1057, hlam, hphi, ht01, ht0b, ht45, ht5b, p1087_1, u1elo1, u4ehi0]
                                    · have p1087_0 := h1087c.1
                                      have p1087_1 := h1087c.2.1
                                      have p1087_2 := h1087c.2.2.1
                                      have p1087_3 := h1087c.2.2.2
                                      linarith only [hlam, p1087_0]
                        · linarith only [h1056, h1076, h768, h955, hc01, hlam, hphi, u1elo3]
                      · linarith only [h0, h1055, h1075, hlam]
                    · linarith only [h0, h1053, h1074, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1116 | h1116
                  · linarith only [h1056, h1057, h1116, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1118 | h1118
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1119 | h1119
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1120 | h1120
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1121 | h1121
                          · linarith only [h1116, h1120, h1121, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1123 | h1123
                            · linarith only [h1053, h1123, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                            · linarith only [h1056, h1057, h1123, hc23, hc35, hlam, hphi]
                        · linarith only [h1056, h1057, h1120, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h1055, h1119, hlam]
                    · linarith only [h0, h1053, h1118, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1129 | h1129
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1130 | h1130
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1131 | h1131
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1132 | h1132
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1133 | h1133
                        · linarith only [h1056, h1129, h1133, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1135 | h1135
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1136 | h1136
                            · linarith only [h1053, h1133, h1136, h768, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1138 | h1138
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1139 | h1139
                                · linarith only [h1054, h1139, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                · linarith only [h1130, h1139, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                              · linarith only [h1129, h1133, h1138, h768, hc23, hc34, hlam, hphi]
                          · linarith only [h1130, h1135, h955, h957, hc01, hlam, hphi, u1elo4]
                      · linarith only [h0, h1055, h1132, hlam]
                    · linarith only [h0, h1053, h1131, hlam]
                  · linarith only [h1056, h1129, h1130, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1147 | h1147
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1148 | h1148
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1149 | h1149
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1150 | h1150
                        · linarith only [h1056, h1150, h768, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1152 | h1152
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1153 | h1153
                            · linarith only [h1053, h1150, h1153, h768, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1155 | h1155
                              · linarith only [h0, h1054, h1129, h1153, h1155, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1157 | h1157
                                · linarith only [h1054, h1157, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                · linarith only [h1147, h1157, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                          · linarith only [h1054, h1147, h1152, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                      · linarith only [h0, h1055, h1149, hlam]
                    · linarith only [h0, h1053, h1054, h1147, h1148, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1163 | h1163
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1164 | h1164
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1165 | h1165
                        · linarith only [h1056, h1165, h768, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1167 | h1167
                          · linarith only [h1147, h1167, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1169 | h1169
                            · linarith only [h1053, h1165, h1167, h1169, h768, hc45, hlam, hphi, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1171 | h1171
                              · linarith only [h0, h1054, h1129, h1169, h1171, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1173 | h1173
                                · linarith only [h0, h1054, h1165, h1167, h1173, h768, hc01, hlam, hphi, u1elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1175 | h1175
                                  · linarith only [h1165, h1167, h1175, h768, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · linarith only [h1165, h1175, h768, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h1055, h1164, hlam]
                    · linarith only [h0, h1053, h1163, h768, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1180 | h1180
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1181 | h1181
                · linarith only [h1053, h1055, h1181, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1183 | h1183
                  · linarith only [h1053, h1055, h1180, h1183, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1185 | h1185
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1186 | h1186
                      · linarith only [h1053, h1055, h1186, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1188 | h1188
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1189 | h1189
                          · linarith only [h1183, h1189, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1191 | h1191
                            · linarith only [h1053, h1191, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                            · linarith only [h1180, h1181, h1191, hc23, hc35, hlam, hphi]
                        · linarith only [h1180, h1188, h768, h955, hc01, hlam, hphi, u1elo3]
                    · linarith only [h0, h1053, h1185, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1196 | h1196
                · linarith only [h1053, h1055, h1196, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1198 | h1198
                  · linarith only [h1054, h1055, h1198, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1200 | h1200
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1201 | h1201
                      · linarith only [h1054, h1055, h1201, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1203 | h1203
                        · linarith only [h1180, h1200, h1201, h1203, h768, hc01, hc25, hlam, hphi, ht12]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1205 | h1205
                          · linarith only [h1054, h1055, h1198, h1205, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1207 | h1207
                            · linarith only [h1053, h1203, h1207, h768, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1209 | h1209
                              · linarith only [h1053, h1054, h1055, h1196, h1209, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1211 | h1211
                                · linarith only [h0, h1054, h1201, h1203, h1205, h1209, h1211, h768, hc03, hc35, hlam, hphi]
                                · linarith only [h0, h1054, h1201, h1211, hc45, hlam, hphi, u4ehi2]
                    · linarith only [h0, h1053, h1054, h1200, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1215 | h1215
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1216 | h1216
              · linarith only [h1053, h1054, h1216, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1218 | h1218
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1219 | h1219
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1220 | h1220
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1221 | h1221
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1222 | h1222
                        · linarith only [h1216, h1218, h1220, h1222, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1224 | h1224
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1225 | h1225
                            · linarith only [h1053, h1054, h1222, h1225, h955, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1227 | h1227
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1228 | h1228
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1229 | h1229
                                  · linarith only [h1053, h1054, h1225, h1227, h1229, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                                  · linarith only [h1053, h1054, h1225, h1229, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h1054, h1219, h1228, h955, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                              · linarith only [h1053, h1054, h1218, h1225, h1227, hc23, hc34, hlam, hphi]
                          · linarith only [h1219, h1224, h955, hlam]
                      · linarith only [h1054, h1215, h1221, hc12, hc24, hlam, hphi]
                    · linarith only [h0, h1053, h1220, hlam]
                  · linarith only [h1054, h1215, h1219, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1238 | h1238
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1239 | h1239
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1240 | h1240
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1241 | h1241
                        · linarith only [h1216, h1241, h768, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1243 | h1243
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1244 | h1244
                            · linarith only [h1053, h1241, h1244, h768, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1246 | h1246
                              · linarith only [h1053, h1218, h1246, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1248 | h1248
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1249 | h1249
                                  · rcases h0bigk with h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [hlam, p1250_0]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h0, hlam, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h768, hlam, p1250_0]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h955, hlam, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h957, hlam, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1054, h1244, hc01, hc34, hlam, hphi, ht12, ht23, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [hlam, p1250_0]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1054, h1244, h768, hc01, hc34, hlam, hphi, ht12, ht23, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1054, hlam, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1054, h1244, h957, hc01, hc34, hlam, hphi, ht12, ht23, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1241, h768, hc01, hc34, hlam, hphi, ht12, ht23, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1053, hlam, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [hlam, p1250_0]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1216, hlam, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1218, hlam, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h955, hc01, hlam, hphi, p1250_1, u1elo3]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1053, h955, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1250_1, u1elo3]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h768, h955, hc01, hlam, hphi, p1250_1, u1elo3]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [hlam, p1250_0]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1215, h1248, h955, hlam, hphi, ht01, ht0b, ht45, ht5b, p1250_1, u1elo3, u4ehi4]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h957, hc01, hlam, hphi, p1250_1, u1elo4]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1215, hlam, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1054, h1215, h1244, h768, hc01, hc34, hlam, hphi, ht12, ht23, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [h1238, hlam, p1250_1]
                                    · have p1250_0 := h1250c.1
                                      have p1250_1 := h1250c.2.1
                                      have p1250_2 := h1250c.2.2.1
                                      have p1250_3 := h1250c.2.2.2
                                      linarith only [hlam, p1250_0]
                                  · linarith only [h1054, h1215, h1244, h1248, h1249, hlam]
                                · linarith only [h1053, h1054, h1248, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h1215, h1238, h1243, h955, hc01, hlam, hphi, u1elo1]
                      · linarith only [h1054, h1215, h1240, hc12, hc24, hlam, hphi]
                    · linarith only [h0, h1053, h1239, hlam]
                  · linarith only [h1054, h1215, h1238, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1282 | h1282
              · linarith only [h1053, h1054, h1282, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1284 | h1284
                · linarith only [h1053, h1215, h1284, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1286 | h1286
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1287 | h1287
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1288 | h1288
                      · linarith only [h1053, h1215, h1288, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1290 | h1290
                        · linarith only [h1282, h1286, h1290, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1292 | h1292
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1293 | h1293
                            · linarith only [h1053, h1290, h1293, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1295 | h1295
                              · linarith only [h1053, h1054, h1284, h1293, h1295, hc03, hc34, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1297 | h1297
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1298 | h1298
                                  · rcases h0bigk with h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [hlam, p1299_0]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h0, hlam, p1299_1]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h768, hlam, p1299_0]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h955, hlam, p1299_1]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h957, hlam, p1299_1]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h0, h1288, h1293, h1297, hc01, hc34, hlam, hphi, ht12, ht23, p1299_1]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [hlam, p1299_0]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h0, h1288, h1293, h1297, h768, hc01, hc34, hlam, hphi, ht12, ht23, p1299_1]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h1054, hlam, p1299_1]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h1215, hlam, p1299_0]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h768, hc01, hlam, hphi, p1299_1, u1elo2]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h1053, hlam, p1299_1]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [hlam, p1299_0]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h1282, hlam, p1299_1]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h1284, hlam, p1299_1]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h955, hc01, hlam, hphi, p1299_1, u1elo3]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h1053, h955, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1299_1, u1elo3]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h768, h955, hc01, hlam, hphi, p1299_1, u1elo3]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [hlam, p1299_0]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h1053, h1215, h955, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1299_1, u1elo3]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h1292, h957, hc01, hlam, hphi, p1299_1, u1elo3]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h1053, h1292, h957, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1299_1, u1elo3]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h1292, h768, h957, hc01, hlam, hphi, p1299_1, u1elo3]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [h1286, hlam, p1299_1]
                                    · have p1299_0 := h1299c.1
                                      have p1299_1 := h1299c.2.1
                                      have p1299_2 := h1299c.2.2.1
                                      have p1299_3 := h1299c.2.2.2
                                      linarith only [hlam, p1299_0]
                                  · linarith only [h0, h1288, h1293, h1297, h1298, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h1054, h1286, h1297, hlam]
                          · linarith only [h1286, h1292, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · linarith only [h0, h1053, h1287, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1329 | h1329
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1330 | h1330
                      · linarith only [h0, h1215, h1330, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1332 | h1332
                        · linarith only [h1282, h1332, h768, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1334 | h1334
                          · linarith only [h1286, h1334, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1336 | h1336
                            · linarith only [h1053, h1332, h1336, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1338 | h1338
                              · linarith only [h1053, h1284, h1338, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1340 | h1340
                                · linarith only [h1334, h1336, h1340, h955, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h1053, h1054, h1340, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h1053, h1054, h1329, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1344 | h1344
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1345 | h1345
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1346 | h1346
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1347 | h1347
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1348 | h1348
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1349 | h1349
                    · linarith only [h1053, h1344, h1349, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1351 | h1351
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1352 | h1352
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1353 | h1353
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1354 | h1354
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1355 | h1355
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1356 | h1356
                                · linarith only [h1344, h1356, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                · linarith only [h1348, h1356, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                              · linarith only [h0, h1344, h1348, h1349, h1355, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h1344, h1348, h1349, h1354, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h1344, h1348, h1353, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                        · linarith only [h1346, h1352, h768, hlam]
                      · linarith only [h0, h1345, h1351, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1364 | h1364
                    · linarith only [h1053, h1345, h1348, h1364, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1366 | h1366
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1367 | h1367
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1368 | h1368
                          · linarith only [h1344, h1348, h1368, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1370 | h1370
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1371 | h1371
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1372 | h1372
                                · linarith only [h1344, h1368, h1372, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1374 | h1374
                                  · linarith only [h1345, h1368, h1370, h1372, h1374, h955, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                  · rcases h0bigk with h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h0, hlam, p1376_1]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h768, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h955, hlam, p1376_1]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h957, hlam, p1376_1]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h0, h1364, hc01, hc23, hlam, hphi, ht12, p1376_1]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1053, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h0, h1364, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1376_1, u4ehi0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h0, h1344, h1348, h1364, h1370, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1376_1, u4ehi3]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h768, hc01, hlam, hphi, p1376_1, u1elo2]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1345, h768, hc25, hlam, hphi, ht01, ht0b, ht5b, p1376_1, u1elo2]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1344, h1370, h768, hlam, hphi, ht01, ht0b, ht45, ht5b, p1376_1, u1elo2, u4ehi3]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1344, h1348, h1370, h768, hlam, hphi, ht01, ht0b, ht45, ht5b, p1376_1, u1elo2, u4ehi3]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h955, hc01, hlam, hphi, p1376_1, u1elo3]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1344, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1346, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1348, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h957, hc01, hlam, hphi, p1376_1, u1elo4]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1345, hlam, p1376_1]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1347, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h0, h1345, h1364, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1376_1, u4ehi0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [hlam, p1376_0]
                              · linarith only [h0, h1364, h1371, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h1344, h1364, h1370, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · linarith only [h1346, h1367, h768, h955, hc01, hlam, hphi, u1elo3]
                      · linarith only [h0, h1345, h1366, hlam]
                · linarith only [h1053, h1345, h1347, hlam]
              · linarith only [h1053, h1344, h1346, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1408 | h1408
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1409 | h1409
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1410 | h1410
                  · linarith only [h1344, h1345, h1410, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1412 | h1412
                    · linarith only [h1053, h1344, h1412, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1414 | h1414
                      · linarith only [h1344, h1345, h1412, h1414, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1416 | h1416
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1417 | h1417
                          · linarith only [h1344, h1345, h1410, h1416, h1417, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1419 | h1419
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1420 | h1420
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1421 | h1421
                                · linarith only [h1344, h1417, h1421, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                                · linarith only [h0, h1344, h1414, h1421, hc45, hlam, hphi, u4ehi2]
                              · linarith only [h1053, h1344, h1409, h1419, h1420, h768, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi3]
                            · linarith only [h0, h1344, h1412, h1419, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · linarith only [h1408, h1416, h768, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1427 | h1427
                  · linarith only [h1053, h1344, h1409, h1427, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1429 | h1429
                    · linarith only [h1053, h1344, h1429, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1431 | h1431
                      · linarith only [h1344, h1345, h1431, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1433 | h1433
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1434 | h1434
                          · linarith only [h1427, h1433, h1434, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1436 | h1436
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1437 | h1437
                              · linarith only [h1053, h1344, h1409, h1436, h1437, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                              · linarith only [h0, h1429, h1437, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h1344, h1429, h1436, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · linarith only [h1408, h1433, h768, h955, hc01, hlam, hphi, u1elo3]
              · linarith only [h1053, h1344, h1408, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1443 | h1443
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1444 | h1444
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1445 | h1445
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1446 | h1446
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1447 | h1447
                    · linarith only [h1053, h1443, h1447, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1449 | h1449
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1450 | h1450
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1451 | h1451
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1452 | h1452
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1453 | h1453
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1454 | h1454
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1455 | h1455
                                  · linarith only [h1444, h1455, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                  · linarith only [h1443, h1454, h1455, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                                · linarith only [h1344, h1444, h1446, h1454, h768, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                              · linarith only [h1447, h1449, h1453, h957, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h1447, h1449, h1452, h957, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h1443, h1446, h1447, h1451, h955, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h1444, h1450, h768, hlam]
                      · linarith only [h1344, h1443, h1449, hc12, hc24, hlam, hphi]
                  · linarith only [h1344, h1443, h1446, hlam]
                · linarith only [h1344, h1443, h1444, h1445, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1466 | h1466
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1467 | h1467
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1468 | h1468
                    · linarith only [h1053, h1443, h1468, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1470 | h1470
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1471 | h1471
                        · linarith only [h1444, h1466, h1471, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1473 | h1473
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1474 | h1474
                            · linarith only [h0, h1468, h1471, h1474, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h1468, h1470, h1474, h957, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1467, h1473, h955, hlam]
                      · linarith only [h1344, h1443, h1470, hc12, hc24, hlam, hphi]
                  · linarith only [h1053, h1443, h1444, h1467, hlam]
                · linarith only [h1053, h1443, h1466, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1481 | h1481
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1482 | h1482
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1483 | h1483
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1484 | h1484
                    · linarith only [h0, h1053, h1484, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1486 | h1486
                      · linarith only [h0, h1443, h1484, h1486, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1488 | h1488
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1489 | h1489
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1490 | h1490
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1491 | h1491
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1492 | h1492
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1493 | h1493
                                  · linarith only [h1481, h1493, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                  · linarith only [h1483, h1493, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                                · linarith only [h1483, h1488, h1492, h955, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
                              · linarith only [h0, h1053, h1482, h1488, h1489, h1491, h957, hc01, hlam, hphi, u1elo2]
                            · linarith only [h0, h1484, h1490, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1483, h1489, h955, hlam]
                        · linarith only [h1481, h1488, h768, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1501 | h1501
                    · linarith only [h0, h1053, h1501, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1503 | h1503
                      · linarith only [h0, h1443, h1503, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1505 | h1505
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1506 | h1506
                          · linarith only [h1483, h1506, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1508 | h1508
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1509 | h1509
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1510 | h1510
                                · linarith only [h1506, h1510, h955, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1512 | h1512
                                  · linarith only [h1481, h1503, h1510, h1512, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                  · rcases h0bigk with h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h0, hlam, p1514_1]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h768, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h955, hlam, p1514_1]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h957, hlam, p1514_1]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1344, hc01, hc24, hlam, hphi, ht12, p1514_1]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1053, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1344, hlam, p1514_1]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1443, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h768, hc01, hlam, hphi, p1514_1, u1elo2]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h0, h768, hc01, hlam, hphi, p1514_1, u1elo2]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1481, h768, hlam, hphi, ht01, ht0b, ht45, ht5b, p1514_1, u1elo2, u4ehi3]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1481, h1483, h768, hlam, hphi, ht01, ht0b, ht45, ht5b, p1514_1, u1elo2, u4ehi3]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h955, hc01, hlam, hphi, p1514_1, u1elo3]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h0, h1344, h1510, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1514_1]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1481, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1483, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h957, hc01, hlam, hphi, p1514_1, u1elo4]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h0, h957, hc01, hlam, hphi, p1514_1, u1elo4]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1482, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1482, h768, hlam, hphi, ht01, ht0b, ht45, ht5b, p1514_1, u1elo2, u4ehi0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [hlam, p1514_0]
                              · linarith only [h1053, h1482, h1509, hlam]
                            · linarith only [h0, h1481, h1501, h1508, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h1481, h1505, h768, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1543 | h1543
                  · linarith only [h1481, h1482, h1543, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1545 | h1545
                    · linarith only [h0, h1053, h1545, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1547 | h1547
                      · linarith only [h0, h1443, h1545, h1547, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1549 | h1549
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1550 | h1550
                          · linarith only [h1543, h1549, h1550, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1552 | h1552
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1553 | h1553
                              · linarith only [h1481, h1482, h1553, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                              · linarith only [h0, h1545, h1553, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h1481, h1545, h1552, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1481, h1482, h1549, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1558 | h1558
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1559 | h1559
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1560 | h1560
                    · linarith only [h0, h1053, h1560, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1562 | h1562
                      · linarith only [h0, h1443, h1560, h1562, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1564 | h1564
                        · linarith only [h1481, h1558, h1559, h1564, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1566 | h1566
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1567 | h1567
                            · linarith only [h0, h1560, h1564, h1567, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h1560, h1567, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1559, h1566, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · linarith only [h1481, h1558, h1559, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1572 | h1572
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1573 | h1573
                    · linarith only [h0, h1053, h1573, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1575 | h1575
                      · linarith only [h0, h1443, h1575, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1577 | h1577
                        · linarith only [h1481, h1577, h768, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1579 | h1579
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1580 | h1580
                            · linarith only [h0, h1573, h1577, h1580, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h1573, h1580, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1572, h1579, h955, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1584 | h1584
                    · linarith only [h0, h1053, h1584, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1586 | h1586
                      · linarith only [h0, h1443, h1586, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1588 | h1588
                        · linarith only [h0, h1053, h1481, h1588, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1590 | h1590
                          · linarith only [h1572, h1590, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1592 | h1592
                            · linarith only [h0, h1584, h1588, h1592, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h1584, h1592, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 3190000 in
set_option maxHeartbeats 3190000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_R_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_R_x1 m hb0 hb1 hb3 hb4 h0

end R2N4
