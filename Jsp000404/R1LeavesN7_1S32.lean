import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S31

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x0_x0_x1 (m : N7Model)
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
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg22356 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg22357 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg22358 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg22359 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg22360 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg22361 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h22362 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h22363 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h22364 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  have h22353 := hg22353
  have h22354 := hg22354
  have h22355 := hg22355
  have h22356 := hg22356
  have h22357 := hg22357
  have h22358 := hg22358
  have h22359 := hg22359
  have h22360 := hg22360
  have h22361 := hg22361
  rcases m.htr 3 4 5 (by decide) (by decide) with h22881 | h22881
  · linarith only [h0, h22350, h22362, h22364, h22881, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
  · rcases h0bigk with h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c | h22883c
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [hlam, p22883_0]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h0, hlam, p22883_1]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h15532, hlam, p22883_0]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h18443, hlam, p22883_1]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h20697, hlam, p22883_1]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      rcases p22883_3 (m.d 0 1) (by simp) with h22889 | h22889
      · linarith only [h0, h22889, hlam]
      · rcases p22883_3 (m.d 0 2) (by simp) with h22891 | h22891
        · rcases p22883_3 (m.d 0 3) (by simp) with h22892 | h22892
          · linarith only [h22350, h22892, hlam]
          · linarith only [h15532, h22892, hlam]
        · linarith only [h0, h22891, hlam]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [hlam, p22883_0]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h0, h22353, h22355, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22883_1]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h0, h22355, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22883_1]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      rcases p22883_3 (m.d 0 1) (by simp) with h22899 | h22899
      · linarith only [h0, h22899, hlam]
      · rcases p22883_3 (m.d 0 2) (by simp) with h22901 | h22901
        · rcases p22883_3 (m.d 0 3) (by simp) with h22902 | h22902
          · linarith only [h22350, h22902, hlam]
          · linarith only [h22354, h22902, hlam]
        · linarith only [h22352, h22901, hlam]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      rcases p22883_3 (m.d 0 1) (by simp) with h22906 | h22906
      · linarith only [h15532, h22906, hlam]
      · rcases p22883_3 (m.d 0 2) (by simp) with h22908 | h22908
        · rcases p22883_3 (m.d 0 3) (by simp) with h22909 | h22909
          · rcases p22883_3 (m.d 0 4) (by simp) with h22910 | h22910
            · linarith only [h22353, h22910, hlam]
            · linarith only [h18443, h22910, hlam]
          · linarith only [h15532, h22909, hlam]
        · linarith only [h0, h22908, hlam]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h22350, hlam, p22883_1]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [hlam, p22883_0]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h22355, h22362, h22364, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p22883_1]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      rcases p22883_3 (m.d 0 1) (by simp) with h22918 | h22918
      · linarith only [h15532, h22918, hlam]
      · rcases p22883_3 (m.d 0 2) (by simp) with h22920 | h22920
        · rcases p22883_3 (m.d 0 3) (by simp) with h22921 | h22921
          · rcases p22883_3 (m.d 0 4) (by simp) with h22922 | h22922
            · linarith only [h22353, h22922, hlam]
            · linarith only [h22355, h22922, hlam]
          · linarith only [h22354, h22921, hlam]
        · linarith only [h22352, h22920, hlam]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      rcases p22883_3 (m.d 0 1) (by simp) with h22927 | h22927
      · linarith only [h18443, h22927, hlam]
      · rcases p22883_3 (m.d 0 2) (by simp) with h22929 | h22929
        · rcases p22883_3 (m.d 0 3) (by simp) with h22930 | h22930
          · rcases p22883_3 (m.d 0 4) (by simp) with h22931 | h22931
            · rcases p22883_3 (m.d 0 5) (by simp) with h22932 | h22932
              · linarith only [h22355, h22932, hlam]
              · linarith only [h20697, h22932, hlam]
            · linarith only [h18443, h22931, hlam]
          · linarith only [h15532, h22930, hlam]
        · linarith only [h0, h22929, hlam]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h22351, hlam, p22883_0]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h22353, hlam, p22883_0]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [hlam, p22883_0]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      rcases p22883_3 (m.d 0 1) (by simp) with h22941 | h22941
      · linarith only [h18443, h22941, hlam]
      · rcases p22883_3 (m.d 0 2) (by simp) with h22943 | h22943
        · rcases p22883_3 (m.d 0 3) (by simp) with h22944 | h22944
          · rcases p22883_3 (m.d 0 4) (by simp) with h22945 | h22945
            · rcases p22883_3 (m.d 0 5) (by simp) with h22946 | h22946
              · linarith only [h22355, h22946, hlam]
              · rcases h2bigk with h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c | h22948c
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [hlam, p22948_0]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h0, hlam, p22948_1]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  rcases p22948_3 (m.d 0 2) (by simp) with h22951 | h22951
                  · rcases p22948_3 (m.d 1 2) (by simp) with h22952 | h22952
                    · rcases p22948_3 (m.d 2 3) (by simp) with h22953 | h22953
                      · linarith only [h22953, hlam, p22948_0]
                      · rcases p22948_3 (m.d 2 4) (by simp) with h22955 | h22955
                        · linarith only [h22351, h22955, hlam]
                        · rcases p22948_3 (m.d 2 5) (by simp) with h22957 | h22957
                          · linarith only [h22352, h22957, hlam]
                          · rcases h3bigk with h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c | h22959c
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h15532, hlam, p22959_1]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              rcases p22959_3 (m.d 0 3) (by simp) with h22962 | h22962
                              · rcases p22959_3 (m.d 1 3) (by simp) with h22963 | h22963
                                · rcases p22959_3 (m.d 2 3) (by simp) with h22964 | h22964
                                  · linarith only [h22350, h22964, hlam]
                                  · rcases p22959_3 (m.d 3 4) (by simp) with h22966 | h22966
                                    · linarith only [h22353, h22966, hlam]
                                    · rcases p22959_3 (m.d 3 5) (by simp) with h22968 | h22968
                                      · linarith only [h22354, h22968, hlam]
                                      · rcases h5bigk with h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c | h22970c
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [hlam, p22970_0]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h20697, hlam, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h18443, h22356, h22359, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22883_1, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h18443, h22356, h22359, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p22883_1, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h18443, h22356, h22359, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22883_1, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h20697, hc01, hc15, hlam, hphi, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [hlam, p22970_0]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          rcases p22970_3 (m.d 0 5) (by simp) with h22978 | h22978
                                          · linarith only [h20697, h22978, hlam]
                                          · linarith only [h22352, h22978, hlam]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          rcases p22970_3 (m.d 0 5) (by simp) with h22981 | h22981
                                          · linarith only [h20697, h22981, hlam]
                                          · linarith only [h22354, h22981, hlam]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h22356, h22359, h22361, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h22352, hlam, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h22358, hlam, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [hlam, p22970_0]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h0, h22352, h22881, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h22364, hlam, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h22354, hlam, p22970_0]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h22360, hlam, p22970_0]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h22363, hlam, p22970_0]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [hlam, p22970_0]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h22881, hlam, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h22355, hlam, p22970_0]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h22361, hlam, p22970_0]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h18443, h22355, h22356, h22359, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [h18443, h22355, h22356, h22359, h22881, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22883_1, p22970_1]
                                        · have p22970_0 := h22970c.1
                                          have p22970_1 := h22970c.2.1
                                          have p22970_2 := h22970c.2.2.1
                                          have p22970_3 := h22970c.2.2.2
                                          linarith only [hlam, p22970_0]
                                · linarith only [h22356, h22963, hlam]
                              · linarith only [h22350, h22962, hlam]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h22353, h22355, h22362, h22364, hlam, p22883_1, p22959_2]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              rcases p22959_3 (m.d 0 3) (by simp) with h23003 | h23003
                              · rcases p22959_3 (m.d 1 3) (by simp) with h23004 | h23004
                                · rcases p22959_3 (m.d 2 3) (by simp) with h23005 | h23005
                                  · linarith only [h22350, h23005, hlam]
                                  · linarith only [h22363, h23005, hlam]
                                · linarith only [h22360, h23004, hlam]
                              · linarith only [h23003, hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h22353, h22355, h22356, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22883_1, p22959_1]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              rcases p22959_3 (m.d 0 3) (by simp) with h23012 | h23012
                              · linarith only [h15532, h23012, hlam]
                              · linarith only [h22350, h23012, hlam]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h15532, h22353, h22355, h22362, h22364, hlam, p22883_1, p22959_2]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              rcases p22959_3 (m.d 0 3) (by simp) with h23016 | h23016
                              · linarith only [h15532, h23016, hlam]
                              · linarith only [h22354, h23016, hlam]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h22350, hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h22356, hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22948_1, p22959_1]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p22948_1, p22959_1]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h22353, hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h22359, hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h22362, hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h22881, hlam, p22959_1]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h22354, hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h22360, hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h22363, hlam, p22959_0]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [h22353, h22354, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p22883_1, p22959_1]
                            · have p22959_0 := h22959c.1
                              have p22959_1 := h22959c.2.1
                              have p22959_2 := h22959c.2.2.1
                              have p22959_3 := h22959c.2.2.2
                              linarith only [hlam, p22959_0]
                    · linarith only [h22356, h22952, hlam]
                  · linarith only [h22951, hlam, p22948_0]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h22350, h22353, h22355, h22364, hlam, p22883_1, p22948_2]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  rcases p22948_3 (m.d 0 2) (by simp) with h23037 | h23037
                  · rcases p22948_3 (m.d 1 2) (by simp) with h23038 | h23038
                    · rcases p22948_3 (m.d 2 3) (by simp) with h23039 | h23039
                      · linarith only [h22350, h23039, hlam]
                      · linarith only [h22363, h23039, hlam]
                    · linarith only [h22358, h23038, hlam]
                  · linarith only [h23037, hlam, p22948_0]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h22350, h22353, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p22883_1, p22948_1]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [hlam, p22948_0]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  rcases p22948_3 (m.d 0 2) (by simp) with h23046 | h23046
                  · linarith only [h0, h23046, hlam]
                  · linarith only [h22350, h23046, hlam]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h0, h22350, h22353, h22355, h22364, hlam, p22883_1, p22948_2]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  rcases p22948_3 (m.d 0 2) (by simp) with h23050 | h23050
                  · linarith only [h0, h23050, hlam]
                  · linarith only [h22352, h23050, hlam]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h22350, hlam, p22948_0]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h22356, hlam, p22948_0]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [hlam, p22948_0]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  rcases p22948_3 (m.d 0 2) (by simp) with h23056 | h23056
                  · rcases p22948_3 (m.d 1 2) (by simp) with h23057 | h23057
                    · rcases p22948_3 (m.d 2 3) (by simp) with h23058 | h23058
                      · rcases p22948_3 (m.d 2 4) (by simp) with h23059 | h23059
                        · linarith only [h22362, h23059, hlam]
                        · rcases p22948_3 (m.d 2 5) (by simp) with h23061 | h23061
                          · linarith only [h22363, h23061, hlam]
                          · linarith only [h22364, h23061, hlam]
                      · linarith only [h22362, h23058, hlam]
                    · linarith only [h22357, h23057, hlam]
                  · linarith only [h22351, h23056, hlam]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  rcases p22948_3 (m.d 0 2) (by simp) with h23067 | h23067
                  · rcases p22948_3 (m.d 1 2) (by simp) with h23068 | h23068
                    · rcases p22948_3 (m.d 2 3) (by simp) with h23069 | h23069
                      · rcases p22948_3 (m.d 2 4) (by simp) with h23070 | h23070
                        · linarith only [h22362, h23070, hlam]
                        · rcases p22948_3 (m.d 2 5) (by simp) with h23072 | h23072
                          · linarith only [h22363, h23072, hlam]
                          · rcases h3bigk with h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c | h23074c
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h15532, hlam, p23074_1]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h0, h22350, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p22948_1, p23074_1]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h22353, h22355, h22362, h22364, hlam, p22883_1, p23074_2]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              rcases p23074_3 (m.d 0 3) (by simp) with h23079 | h23079
                              · rcases p23074_3 (m.d 1 3) (by simp) with h23080 | h23080
                                · rcases p23074_3 (m.d 2 3) (by simp) with h23081 | h23081
                                  · linarith only [h22350, h23081, hlam]
                                  · linarith only [h22363, h23081, hlam]
                                · linarith only [h22360, h23080, hlam]
                              · linarith only [h23079, hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h22353, h22355, h22356, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22883_1, p23074_1]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h22356, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p22948_1, p23074_1]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h15532, h22353, h22355, h22362, h22364, hlam, p22883_1, p23074_2]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              rcases p23074_3 (m.d 0 3) (by simp) with h23090 | h23090
                              · linarith only [h15532, h23090, hlam]
                              · linarith only [h22354, h23090, hlam]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h22350, hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h22356, hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              rcases p23074_3 (m.d 0 3) (by simp) with h23096 | h23096
                              · rcases p23074_3 (m.d 1 3) (by simp) with h23097 | h23097
                                · rcases p23074_3 (m.d 2 3) (by simp) with h23098 | h23098
                                  · rcases p23074_3 (m.d 3 4) (by simp) with h23099 | h23099
                                    · linarith only [h23099, hlam, p23074_0]
                                    · rcases p23074_3 (m.d 3 5) (by simp) with h23101 | h23101
                                      · linarith only [h22363, h23101, hlam]
                                      · linarith only [h22881, h23101, hlam]
                                  · linarith only [h23098, hlam, p23074_0]
                                · linarith only [h22359, h23097, hlam]
                              · linarith only [h22353, h23096, hlam]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              rcases p23074_3 (m.d 0 3) (by simp) with h23107 | h23107
                              · rcases p23074_3 (m.d 1 3) (by simp) with h23108 | h23108
                                · rcases p23074_3 (m.d 2 3) (by simp) with h23109 | h23109
                                  · rcases p23074_3 (m.d 3 4) (by simp) with h23110 | h23110
                                    · linarith only [h22362, h23110, hlam]
                                    · rcases p23074_3 (m.d 3 5) (by simp) with h23112 | h23112
                                      · linarith only [h23112, hlam, p23074_0]
                                      · rcases h5bigk with h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [hlam, p23114_0]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h20697, hlam, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h22353, hc03, hc25, hlam, hphi, ht0b, ht5b, p22883_1, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h0, h22350, h22353, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p22883_1, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h0, h22350, h22353, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22883_1, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h20697, h22359, h22361, hc01, hc13, hlam, hphi, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [hlam, p23114_0]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          rcases p23114_3 (m.d 0 5) (by simp) with h23122 | h23122
                                          · linarith only [h20697, h23122, hlam]
                                          · linarith only [h22352, h23122, hlam]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          rcases p23114_3 (m.d 0 5) (by simp) with h23125 | h23125
                                          · linarith only [h20697, h23125, hlam]
                                          · linarith only [h22354, h23125, hlam]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h22356, h22359, h22361, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h22352, hlam, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h22358, hlam, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [hlam, p23114_0]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h22881, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22948_1, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h22364, hlam, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h22354, hlam, p23114_0]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h22360, hlam, p23114_0]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h22363, hlam, p23114_0]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [hlam, p23114_0]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h22881, hlam, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h22355, hlam, p23114_0]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h22361, hlam, p23114_0]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h0, h22350, h22353, h22355, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [h0, h22350, h22353, h22355, h22881, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22883_1, p23114_1]
                                        · have p23114_0 := h23114c.1
                                          have p23114_1 := h23114c.2.1
                                          have p23114_2 := h23114c.2.2.1
                                          have p23114_3 := h23114c.2.2.2
                                          linarith only [hlam, p23114_0]
                                  · linarith only [h23109, hlam, p23074_0]
                                · linarith only [h22360, h23108, hlam]
                              · linarith only [h22354, h23107, hlam]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h22353, hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h22359, hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h22362, hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h22881, hlam, p23074_1]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h22354, hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h22360, hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h22363, hlam, p23074_0]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [h0, h22350, h22352, h22353, h22363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22883_1, p23074_1]
                            · have p23074_0 := h23074c.1
                              have p23074_1 := h23074c.2.1
                              have p23074_2 := h23074c.2.2.1
                              have p23074_3 := h23074c.2.2.2
                              linarith only [hlam, p23074_0]
                      · linarith only [h22363, h23069, hlam]
                    · linarith only [h22358, h23068, hlam]
                  · linarith only [h22352, h23067, hlam]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h22351, hlam, p22948_0]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h22357, hlam, p22948_0]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h22362, hlam, p22948_1]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [hlam, p22948_0]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h22364, hlam, p22948_1]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h22352, hlam, p22948_0]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h22358, hlam, p22948_0]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h22363, hlam, p22948_1]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [h0, h22350, h22353, h22355, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22883_1, p22948_1]
                · have p22948_0 := h22948c.1
                  have p22948_1 := h22948c.2.1
                  have p22948_2 := h22948c.2.2.1
                  have p22948_3 := h22948c.2.2.2
                  linarith only [hlam, p22948_0]
            · linarith only [h22355, h22945, hlam]
          · linarith only [h22354, h22944, hlam]
        · linarith only [h22352, h22943, hlam]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      rcases p22883_3 (m.d 0 1) (by simp) with h23173 | h23173
      · linarith only [h20697, h23173, hlam]
      · rcases p22883_3 (m.d 0 2) (by simp) with h23175 | h23175
        · rcases p22883_3 (m.d 0 3) (by simp) with h23176 | h23176
          · rcases p22883_3 (m.d 0 4) (by simp) with h23177 | h23177
            · rcases p22883_3 (m.d 0 5) (by simp) with h23178 | h23178
              · rcases h2bigk with h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c | h23179c
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [h0, hlam, p23179_1]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  rcases p23179_3 (m.d 0 2) (by simp) with h23182 | h23182
                  · rcases p23179_3 (m.d 1 2) (by simp) with h23183 | h23183
                    · rcases p23179_3 (m.d 2 3) (by simp) with h23184 | h23184
                      · linarith only [h23184, hlam, p23179_0]
                      · rcases p23179_3 (m.d 2 4) (by simp) with h23186 | h23186
                        · linarith only [h22351, h23186, hlam]
                        · rcases p23179_3 (m.d 2 5) (by simp) with h23188 | h23188
                          · linarith only [h22352, h23188, hlam]
                          · rcases h3bigk with h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c | h23190c
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h15532, hlam, p23190_1]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              rcases p23190_3 (m.d 0 3) (by simp) with h23193 | h23193
                              · rcases p23190_3 (m.d 1 3) (by simp) with h23194 | h23194
                                · rcases p23190_3 (m.d 2 3) (by simp) with h23195 | h23195
                                  · linarith only [h22350, h23195, hlam]
                                  · rcases p23190_3 (m.d 3 4) (by simp) with h23197 | h23197
                                    · linarith only [h22353, h23197, hlam]
                                    · rcases p23190_3 (m.d 3 5) (by simp) with h23199 | h23199
                                      · linarith only [h22354, h23199, hlam]
                                      · rcases h5bigk with h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c | h23201c
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [hlam, p23201_0]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h20697, hlam, p23201_1]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          rcases p23201_3 (m.d 0 5) (by simp) with h23204 | h23204
                                          · rcases p23201_3 (m.d 1 5) (by simp) with h23205 | h23205
                                            · rcases p23201_3 (m.d 2 5) (by simp) with h23206 | h23206
                                              · linarith only [h22352, h23206, hlam]
                                              · rcases p23201_3 (m.d 3 5) (by simp) with h23208 | h23208
                                                · linarith only [h22354, h23208, hlam]
                                                · rcases p23201_3 (m.d 4 5) (by simp) with h23210 | h23210
                                                  · linarith only [h22355, h23210, hlam]
                                                  · linarith only [h22364, h23210, hlam]
                                            · linarith only [h22358, h23205, hlam]
                                          · linarith only [h22352, h23204, hlam]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          rcases p23201_3 (m.d 0 5) (by simp) with h23215 | h23215
                                          · rcases p23201_3 (m.d 1 5) (by simp) with h23216 | h23216
                                            · rcases p23201_3 (m.d 2 5) (by simp) with h23217 | h23217
                                              · linarith only [h22352, h23217, hlam]
                                              · linarith only [h22363, h23217, hlam]
                                            · linarith only [h22360, h23216, hlam]
                                          · linarith only [h22354, h23215, hlam]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h22362, h22364, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p23201_1]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h22356, h22359, h22361, hc01, hc12, hlam, hphi, p22883_1, p23201_1]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [hlam, p23201_0]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          rcases p23201_3 (m.d 0 5) (by simp) with h23225 | h23225
                                          · linarith only [h20697, h23225, hlam]
                                          · linarith only [h22352, h23225, hlam]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          rcases p23201_3 (m.d 0 5) (by simp) with h23228 | h23228
                                          · linarith only [h20697, h23228, hlam]
                                          · linarith only [h22354, h23228, hlam]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h22356, h22359, h22361, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23201_1]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h22352, hlam, p23201_1]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h22358, hlam, p23201_1]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [hlam, p23201_0]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h0, h22352, h22881, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23201_1]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h22364, hlam, p23201_1]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h22354, hlam, p23201_0]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h22360, hlam, p23201_0]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h22363, hlam, p23201_0]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [hlam, p23201_0]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h22881, hlam, p23201_1]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h22355, hlam, p23201_0]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h22361, hlam, p23201_0]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h0, h22350, h22353, h22355, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p23201_1]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [h0, h22350, h22353, h22355, h22881, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23201_1]
                                        · have p23201_0 := h23201c.1
                                          have p23201_1 := h23201c.2.1
                                          have p23201_2 := h23201c.2.2.1
                                          have p23201_3 := h23201c.2.2.2
                                          linarith only [hlam, p23201_0]
                                · linarith only [h22356, h23194, hlam]
                              · linarith only [h22350, h23193, hlam]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              rcases p23190_3 (m.d 0 3) (by simp) with h23249 | h23249
                              · rcases p23190_3 (m.d 1 3) (by simp) with h23250 | h23250
                                · rcases p23190_3 (m.d 2 3) (by simp) with h23251 | h23251
                                  · linarith only [h22350, h23251, hlam]
                                  · linarith only [h22362, h23251, hlam]
                                · linarith only [h22359, h23250, hlam]
                              · linarith only [h23249, hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              rcases p23190_3 (m.d 0 3) (by simp) with h23256 | h23256
                              · rcases p23190_3 (m.d 1 3) (by simp) with h23257 | h23257
                                · rcases p23190_3 (m.d 2 3) (by simp) with h23258 | h23258
                                  · linarith only [h22350, h23258, hlam]
                                  · linarith only [h22363, h23258, hlam]
                                · linarith only [h22360, h23257, hlam]
                              · linarith only [h23256, hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h22354, h22356, hc01, hc12, hlam, hphi, p22883_1, p23190_1]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              rcases p23190_3 (m.d 0 3) (by simp) with h23265 | h23265
                              · linarith only [h15532, h23265, hlam]
                              · linarith only [h22350, h23265, hlam]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              rcases p23190_3 (m.d 0 3) (by simp) with h23268 | h23268
                              · linarith only [h15532, h23268, hlam]
                              · linarith only [h22353, h23268, hlam]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              rcases p23190_3 (m.d 0 3) (by simp) with h23271 | h23271
                              · linarith only [h15532, h23271, hlam]
                              · linarith only [h22354, h23271, hlam]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h22350, hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h22356, hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23179_1, p23190_1]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p23179_1, p23190_1]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h22353, hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h22359, hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h22362, hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h22881, hlam, p23190_1]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h22354, hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h22360, hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h22363, hlam, p23190_0]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [h0, h22363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23179_1, p23190_1]
                            · have p23190_0 := h23190c.1
                              have p23190_1 := h23190c.2.1
                              have p23190_2 := h23190c.2.2.1
                              have p23190_3 := h23190c.2.2.2
                              linarith only [hlam, p23190_0]
                    · linarith only [h22356, h23183, hlam]
                  · linarith only [h23182, hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  rcases p23179_3 (m.d 0 2) (by simp) with h23291 | h23291
                  · rcases p23179_3 (m.d 1 2) (by simp) with h23292 | h23292
                    · rcases p23179_3 (m.d 2 3) (by simp) with h23293 | h23293
                      · linarith only [h22350, h23293, hlam]
                      · linarith only [h22362, h23293, hlam]
                    · linarith only [h22357, h23292, hlam]
                  · linarith only [h23291, hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  rcases p23179_3 (m.d 0 2) (by simp) with h23298 | h23298
                  · rcases p23179_3 (m.d 1 2) (by simp) with h23299 | h23299
                    · rcases p23179_3 (m.d 2 3) (by simp) with h23300 | h23300
                      · linarith only [h22350, h23300, hlam]
                      · linarith only [h22363, h23300, hlam]
                    · linarith only [h22358, h23299, hlam]
                  · linarith only [h23298, hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [h22350, h22353, h22355, hc01, hc12, hlam, hphi, p22883_1, p23179_1]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  rcases p23179_3 (m.d 0 2) (by simp) with h23307 | h23307
                  · linarith only [h0, h23307, hlam]
                  · linarith only [h22350, h23307, hlam]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  rcases p23179_3 (m.d 0 2) (by simp) with h23310 | h23310
                  · linarith only [h0, h23310, hlam]
                  · linarith only [h22351, h23310, hlam]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  rcases p23179_3 (m.d 0 2) (by simp) with h23313 | h23313
                  · linarith only [h0, h23313, hlam]
                  · linarith only [h22352, h23313, hlam]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [h22350, hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [h22356, hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  rcases p23179_3 (m.d 0 2) (by simp) with h23319 | h23319
                  · rcases p23179_3 (m.d 1 2) (by simp) with h23320 | h23320
                    · rcases p23179_3 (m.d 2 3) (by simp) with h23321 | h23321
                      · rcases p23179_3 (m.d 2 4) (by simp) with h23322 | h23322
                        · linarith only [h22362, h23322, hlam]
                        · rcases p23179_3 (m.d 2 5) (by simp) with h23324 | h23324
                          · linarith only [h22363, h23324, hlam]
                          · linarith only [h22364, h23324, hlam]
                      · linarith only [h22362, h23321, hlam]
                    · linarith only [h22357, h23320, hlam]
                  · linarith only [h22351, h23319, hlam]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  rcases p23179_3 (m.d 0 2) (by simp) with h23330 | h23330
                  · rcases p23179_3 (m.d 1 2) (by simp) with h23331 | h23331
                    · rcases p23179_3 (m.d 2 3) (by simp) with h23332 | h23332
                      · rcases p23179_3 (m.d 2 4) (by simp) with h23333 | h23333
                        · linarith only [h22362, h23333, hlam]
                        · rcases p23179_3 (m.d 2 5) (by simp) with h23335 | h23335
                          · linarith only [h22363, h23335, hlam]
                          · rcases h3bigk with h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c | h23337c
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h15532, hlam, p23337_1]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h22364, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p23179_1, p23337_1]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              rcases p23337_3 (m.d 0 3) (by simp) with h23341 | h23341
                              · rcases p23337_3 (m.d 1 3) (by simp) with h23342 | h23342
                                · rcases p23337_3 (m.d 2 3) (by simp) with h23343 | h23343
                                  · linarith only [h22350, h23343, hlam]
                                  · linarith only [h22362, h23343, hlam]
                                · linarith only [h22359, h23342, hlam]
                              · linarith only [h23341, hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              rcases p23337_3 (m.d 0 3) (by simp) with h23348 | h23348
                              · rcases p23337_3 (m.d 1 3) (by simp) with h23349 | h23349
                                · rcases p23337_3 (m.d 2 3) (by simp) with h23350 | h23350
                                  · linarith only [h22350, h23350, hlam]
                                  · linarith only [h22363, h23350, hlam]
                                · linarith only [h22360, h23349, hlam]
                              · linarith only [h23348, hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h22350, h22356, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23179_1, p23337_1]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h22356, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23179_1, p23337_1]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              rcases p23337_3 (m.d 0 3) (by simp) with h23358 | h23358
                              · linarith only [h15532, h23358, hlam]
                              · linarith only [h22353, h23358, hlam]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              rcases p23337_3 (m.d 0 3) (by simp) with h23361 | h23361
                              · linarith only [h15532, h23361, hlam]
                              · linarith only [h22354, h23361, hlam]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h22350, hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h22356, hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              rcases p23337_3 (m.d 0 3) (by simp) with h23367 | h23367
                              · rcases p23337_3 (m.d 1 3) (by simp) with h23368 | h23368
                                · rcases p23337_3 (m.d 2 3) (by simp) with h23369 | h23369
                                  · rcases p23337_3 (m.d 3 4) (by simp) with h23370 | h23370
                                    · linarith only [h23370, hlam, p23337_0]
                                    · rcases p23337_3 (m.d 3 5) (by simp) with h23372 | h23372
                                      · linarith only [h22363, h23372, hlam]
                                      · linarith only [h22881, h23372, hlam]
                                  · linarith only [h23369, hlam, p23337_0]
                                · linarith only [h22359, h23368, hlam]
                              · linarith only [h22353, h23367, hlam]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              rcases p23337_3 (m.d 0 3) (by simp) with h23378 | h23378
                              · rcases p23337_3 (m.d 1 3) (by simp) with h23379 | h23379
                                · rcases p23337_3 (m.d 2 3) (by simp) with h23380 | h23380
                                  · rcases p23337_3 (m.d 3 4) (by simp) with h23381 | h23381
                                    · linarith only [h22362, h23381, hlam]
                                    · rcases p23337_3 (m.d 3 5) (by simp) with h23383 | h23383
                                      · linarith only [h23383, hlam, p23337_0]
                                      · rcases h5bigk with h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c | h23385c
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [hlam, p23385_0]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h20697, hlam, p23385_1]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          rcases p23385_3 (m.d 0 5) (by simp) with h23388 | h23388
                                          · rcases p23385_3 (m.d 1 5) (by simp) with h23389 | h23389
                                            · rcases p23385_3 (m.d 2 5) (by simp) with h23390 | h23390
                                              · linarith only [h22352, h23390, hlam]
                                              · rcases p23385_3 (m.d 3 5) (by simp) with h23392 | h23392
                                                · linarith only [h22354, h23392, hlam]
                                                · rcases p23385_3 (m.d 4 5) (by simp) with h23394 | h23394
                                                  · linarith only [h22355, h23394, hlam]
                                                  · linarith only [h22364, h23394, hlam]
                                            · linarith only [h22358, h23389, hlam]
                                          · linarith only [h22352, h23388, hlam]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          rcases p23385_3 (m.d 0 5) (by simp) with h23399 | h23399
                                          · rcases p23385_3 (m.d 1 5) (by simp) with h23400 | h23400
                                            · rcases p23385_3 (m.d 2 5) (by simp) with h23401 | h23401
                                              · linarith only [h22352, h23401, hlam]
                                              · linarith only [h22363, h23401, hlam]
                                            · linarith only [h22360, h23400, hlam]
                                          · linarith only [h22354, h23399, hlam]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22350, h22353, h22355, h22362, h22364, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p23385_1]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22361, hc01, hc14, hlam, hphi, p22883_1, p23385_1]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [hlam, p23385_0]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          rcases p23385_3 (m.d 0 5) (by simp) with h23409 | h23409
                                          · linarith only [h20697, h23409, hlam]
                                          · linarith only [h22352, h23409, hlam]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          rcases p23385_3 (m.d 0 5) (by simp) with h23412 | h23412
                                          · linarith only [h20697, h23412, hlam]
                                          · linarith only [h22354, h23412, hlam]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22356, h22359, h22361, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23385_1]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22352, hlam, p23385_1]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22358, hlam, p23385_1]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [hlam, p23385_0]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22881, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p23179_1, p23385_1]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22364, hlam, p23385_1]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22354, hlam, p23385_0]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22360, hlam, p23385_0]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22363, hlam, p23385_0]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [hlam, p23385_0]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22881, hlam, p23385_1]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22355, hlam, p23385_0]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h22361, hlam, p23385_0]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h0, h22350, h22353, h22355, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p23385_1]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [h0, h22350, h22353, h22355, h22881, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23385_1]
                                        · have p23385_0 := h23385c.1
                                          have p23385_1 := h23385c.2.1
                                          have p23385_2 := h23385c.2.2.1
                                          have p23385_3 := h23385c.2.2.2
                                          linarith only [hlam, p23385_0]
                                  · linarith only [h23380, hlam, p23337_0]
                                · linarith only [h22360, h23379, hlam]
                              · linarith only [h22354, h23378, hlam]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h22353, hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h22359, hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h22362, hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h22881, hlam, p23337_1]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h22354, hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h22360, hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h22363, hlam, p23337_0]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [h0, h22350, h22363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23337_1]
                            · have p23337_0 := h23337c.1
                              have p23337_1 := h23337c.2.1
                              have p23337_2 := h23337c.2.2.1
                              have p23337_3 := h23337c.2.2.2
                              linarith only [hlam, p23337_0]
                      · linarith only [h22363, h23332, hlam]
                    · linarith only [h22358, h23331, hlam]
                  · linarith only [h22352, h23330, hlam]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [h22351, hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [h22357, hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [h22362, hlam, p23179_1]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [h22364, hlam, p23179_1]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [h22352, hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [h22358, hlam, p23179_0]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [h22363, hlam, p23179_1]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  rcases p23179_3 (m.d 0 2) (by simp) with h23455 | h23455
                  · rcases p23179_3 (m.d 1 2) (by simp) with h23456 | h23456
                    · rcases p23179_3 (m.d 2 3) (by simp) with h23457 | h23457
                      · rcases p23179_3 (m.d 2 4) (by simp) with h23458 | h23458
                        · linarith only [h22364, h23458, hlam]
                        · rcases p23179_3 (m.d 2 5) (by simp) with h23460 | h23460
                          · rcases h3bigk with h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c | h23461c
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h15532, hlam, p23461_1]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h0, h22350, h22362, h22363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23179_1, p23461_1]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h22353, h22355, h22362, h22364, hlam, p23179_1, p23461_2]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              rcases p23461_3 (m.d 0 3) (by simp) with h23466 | h23466
                              · rcases p23461_3 (m.d 1 3) (by simp) with h23467 | h23467
                                · rcases p23461_3 (m.d 2 3) (by simp) with h23468 | h23468
                                  · linarith only [h22350, h23468, hlam]
                                  · linarith only [h22363, h23468, hlam]
                                · linarith only [h22360, h23467, hlam]
                              · linarith only [h23466, hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h22353, h22355, h22356, h22364, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p23179_1, p23461_1]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h22356, h22362, h22363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23179_1, p23461_1]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h15532, h22353, h22355, h22362, h22364, hlam, p23179_1, p23461_2]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              rcases p23461_3 (m.d 0 3) (by simp) with h23477 | h23477
                              · linarith only [h15532, h23477, hlam]
                              · linarith only [h22354, h23477, hlam]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h22350, hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h22356, hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              rcases p23461_3 (m.d 0 3) (by simp) with h23483 | h23483
                              · rcases p23461_3 (m.d 1 3) (by simp) with h23484 | h23484
                                · rcases p23461_3 (m.d 2 3) (by simp) with h23485 | h23485
                                  · rcases p23461_3 (m.d 3 4) (by simp) with h23486 | h23486
                                    · linarith only [h23486, hlam, p23461_0]
                                    · rcases p23461_3 (m.d 3 5) (by simp) with h23488 | h23488
                                      · linarith only [h22363, h23488, hlam]
                                      · linarith only [h22881, h23488, hlam]
                                  · linarith only [h23485, hlam, p23461_0]
                                · linarith only [h22359, h23484, hlam]
                              · linarith only [h22353, h23483, hlam]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              rcases p23461_3 (m.d 0 3) (by simp) with h23494 | h23494
                              · rcases p23461_3 (m.d 1 3) (by simp) with h23495 | h23495
                                · rcases p23461_3 (m.d 2 3) (by simp) with h23496 | h23496
                                  · rcases p23461_3 (m.d 3 4) (by simp) with h23497 | h23497
                                    · linarith only [h22362, h23497, hlam]
                                    · rcases p23461_3 (m.d 3 5) (by simp) with h23499 | h23499
                                      · linarith only [h23499, hlam, p23461_0]
                                      · rcases h5bigk with h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c | h23501c
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [hlam, p23501_0]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h20697, hlam, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22362, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p23179_1, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          rcases p23501_3 (m.d 0 5) (by simp) with h23505 | h23505
                                          · rcases p23501_3 (m.d 1 5) (by simp) with h23506 | h23506
                                            · rcases p23501_3 (m.d 2 5) (by simp) with h23507 | h23507
                                              · linarith only [h22352, h23507, hlam]
                                              · linarith only [h22363, h23507, hlam]
                                            · linarith only [h22360, h23506, hlam]
                                          · linarith only [h22354, h23505, hlam]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22362, h22364, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p23179_1, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22359, h22361, hc01, hc13, hlam, hphi, p22883_1, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [hlam, p23501_0]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22356, h22359, h22361, h22362, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23179_1, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          rcases p23501_3 (m.d 0 5) (by simp) with h23516 | h23516
                                          · linarith only [h20697, h23516, hlam]
                                          · linarith only [h22354, h23516, hlam]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22356, h22359, h22361, h22362, h22364, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23179_1, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22352, hlam, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22358, hlam, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [hlam, p23501_0]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22353, h22355, h22364, h22881, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22364, hlam, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22354, hlam, p23501_0]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22360, hlam, p23501_0]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22363, hlam, p23501_0]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [hlam, p23501_0]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22881, hlam, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22355, hlam, p23501_0]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22361, hlam, p23501_0]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h22353, h22355, hc03, hc25, hlam, hphi, ht0b, ht5b, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [h15532, h22353, h22355, h22356, h22881, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23501_1]
                                        · have p23501_0 := h23501c.1
                                          have p23501_1 := h23501c.2.1
                                          have p23501_2 := h23501c.2.2.1
                                          have p23501_3 := h23501c.2.2.2
                                          linarith only [hlam, p23501_0]
                                  · linarith only [h23496, hlam, p23461_0]
                                · linarith only [h22360, h23495, hlam]
                              · linarith only [h22354, h23494, hlam]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h22353, hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h22359, hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h22362, hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h22881, hlam, p23461_1]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h22354, hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h22360, hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h22363, hlam, p23461_0]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [h0, h22350, h22363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23461_1]
                            · have p23461_0 := h23461c.1
                              have p23461_1 := h23461c.2.1
                              have p23461_2 := h23461c.2.2.1
                              have p23461_3 := h23461c.2.2.2
                              linarith only [hlam, p23461_0]
                          · linarith only [h22364, h23460, hlam]
                      · linarith only [h22362, h23457, hlam]
                    · linarith only [h22357, h23456, hlam]
                  · linarith only [h22351, h23455, hlam]
                · have p23179_0 := h23179c.1
                  have p23179_1 := h23179c.2.1
                  have p23179_2 := h23179c.2.2.1
                  have p23179_3 := h23179c.2.2.2
                  linarith only [hlam, p23179_0]
              · linarith only [h20697, h23178, hlam]
            · linarith only [h18443, h23177, hlam]
          · linarith only [h15532, h23176, hlam]
        · linarith only [h0, h23175, hlam]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h22352, hlam, p22883_1]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h22354, hlam, p22883_0]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [h22355, hlam, p22883_1]
    · have p22883_0 := h22883c.1
      have p22883_1 := h22883c.2.1
      have p22883_2 := h22883c.2.2.1
      have p22883_3 := h22883c.2.2.2
      linarith only [hlam, p22883_0]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x0_x0 (m : N7Model)
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
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg22356 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg22357 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg22358 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg22359 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg22360 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg22361 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h22362 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h22363 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  have h22353 := hg22353
  have h22354 := hg22354
  have h22355 := hg22355
  have h22356 := hg22356
  have h22357 := hg22357
  have h22358 := hg22358
  have h22359 := hg22359
  have h22360 := hg22360
  have h22361 := hg22361
  rcases m.htr 2 4 5 (by decide) (by decide) with h22364 | h22364
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h22363 h22364
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h22363 h22364

end R2N4
