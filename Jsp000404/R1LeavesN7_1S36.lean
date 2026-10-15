import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S33
import Jsp000404.R1LeavesN7_1S35

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x1 (m : N7Model)
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
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  rcases m.htr 3 4 5 (by decide) (by decide) with h24874 | h24874
  · rcases h0bigk with h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c | h24875c
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [hlam, p24875_0]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h0, hlam, p24875_1]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h15532, hlam, p24875_0]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h18443, hlam, p24875_1]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h20697, hlam, p24875_1]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      rcases p24875_3 (m.d 0 1) (by simp) with h24881 | h24881
      · linarith only [h0, h24881, hlam]
      · rcases p24875_3 (m.d 0 2) (by simp) with h24883 | h24883
        · rcases p24875_3 (m.d 0 3) (by simp) with h24884 | h24884
          · linarith only [h22350, h24884, hlam]
          · linarith only [h15532, h24884, hlam]
        · linarith only [h0, h24883, hlam]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [hlam, p24875_0]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h0, h22353, h24024, h24874, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p24875_1]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h0, h22353, h24024, h24874, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p24875_1]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      rcases p24875_3 (m.d 0 1) (by simp) with h24891 | h24891
      · linarith only [h0, h24891, hlam]
      · rcases p24875_3 (m.d 0 2) (by simp) with h24893 | h24893
        · rcases p24875_3 (m.d 0 3) (by simp) with h24894 | h24894
          · linarith only [h22350, h24894, hlam]
          · linarith only [h22354, h24894, hlam]
        · linarith only [h22352, h24893, hlam]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      rcases p24875_3 (m.d 0 1) (by simp) with h24898 | h24898
      · linarith only [h15532, h24898, hlam]
      · rcases p24875_3 (m.d 0 2) (by simp) with h24900 | h24900
        · rcases p24875_3 (m.d 0 3) (by simp) with h24901 | h24901
          · rcases p24875_3 (m.d 0 4) (by simp) with h24902 | h24902
            · linarith only [h22353, h24902, hlam]
            · linarith only [h18443, h24902, hlam]
          · linarith only [h15532, h24901, hlam]
        · linarith only [h0, h24900, hlam]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h22350, hlam, p24875_1]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [hlam, p24875_0]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h22353, h22362, h24024, h24874, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24875_1]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      rcases p24875_3 (m.d 0 1) (by simp) with h24910 | h24910
      · linarith only [h15532, h24910, hlam]
      · rcases p24875_3 (m.d 0 2) (by simp) with h24912 | h24912
        · rcases p24875_3 (m.d 0 3) (by simp) with h24913 | h24913
          · rcases p24875_3 (m.d 0 4) (by simp) with h24914 | h24914
            · linarith only [h22353, h24914, hlam]
            · linarith only [h22355, h24914, hlam]
          · linarith only [h22354, h24913, hlam]
        · linarith only [h22352, h24912, hlam]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      rcases p24875_3 (m.d 0 1) (by simp) with h24919 | h24919
      · linarith only [h18443, h24919, hlam]
      · rcases p24875_3 (m.d 0 2) (by simp) with h24921 | h24921
        · rcases p24875_3 (m.d 0 3) (by simp) with h24922 | h24922
          · rcases p24875_3 (m.d 0 4) (by simp) with h24923 | h24923
            · rcases p24875_3 (m.d 0 5) (by simp) with h24924 | h24924
              · linarith only [h22355, h24924, hlam]
              · linarith only [h20697, h24924, hlam]
            · linarith only [h18443, h24923, hlam]
          · linarith only [h15532, h24922, hlam]
        · linarith only [h0, h24921, hlam]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h22351, hlam, p24875_0]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h22353, hlam, p24875_0]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [hlam, p24875_0]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      rcases p24875_3 (m.d 0 1) (by simp) with h24933 | h24933
      · linarith only [h18443, h24933, hlam]
      · rcases p24875_3 (m.d 0 2) (by simp) with h24935 | h24935
        · rcases p24875_3 (m.d 0 3) (by simp) with h24936 | h24936
          · rcases p24875_3 (m.d 0 4) (by simp) with h24937 | h24937
            · rcases p24875_3 (m.d 0 5) (by simp) with h24938 | h24938
              · linarith only [h22355, h24938, hlam]
              · rcases h2bigk with h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c | h24940c
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h0, hlam, p24940_1]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h22350, h22353, h22362, h24024, h24874, hlam, p24940_2]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h22350, h22353, h24024, h24874, hlam, p24940_2]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  rcases p24940_3 (m.d 0 2) (by simp) with h24945 | h24945
                  · rcases p24940_3 (m.d 1 2) (by simp) with h24946 | h24946
                    · rcases p24940_3 (m.d 2 3) (by simp) with h24947 | h24947
                      · linarith only [h22350, h24947, hlam]
                      · rcases p24940_3 (m.d 2 4) (by simp) with h24949 | h24949
                        · linarith only [h22351, h24949, hlam]
                        · rcases p24940_3 (m.d 2 5) (by simp) with h24951 | h24951
                          · linarith only [h24951, hlam, p24940_0]
                          · rcases h3bigk with h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c | h24953c
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h15532, hlam, p24953_1]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22353, h22354, h22362, h24024, h24874, hlam, p24875_1, p24953_2]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22350, h22362, h24024, h24874, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24953_1]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              rcases p24953_3 (m.d 0 3) (by simp) with h24958 | h24958
                              · rcases p24953_3 (m.d 1 3) (by simp) with h24959 | h24959
                                · rcases p24953_3 (m.d 2 3) (by simp) with h24960 | h24960
                                  · linarith only [h22350, h24960, hlam]
                                  · rcases p24953_3 (m.d 3 4) (by simp) with h24962 | h24962
                                    · linarith only [h22353, h24962, hlam]
                                    · linarith only [h24874, h24962, hlam]
                                · linarith only [h22360, h24959, hlam]
                              · linarith only [h24958, hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22353, h22356, h22362, h24024, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24953_1]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h15532, h22353, h22354, h22362, h24024, h24874, hlam, p24875_1, p24953_2]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22362, h24024, h24874, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24953_1]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              rcases p24953_3 (m.d 0 3) (by simp) with h24971 | h24971
                              · linarith only [h15532, h24971, hlam]
                              · linarith only [h22354, h24971, hlam]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22350, hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22356, hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22362, hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h23731, hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22353, hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22359, hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              rcases p24953_3 (m.d 0 3) (by simp) with h24981 | h24981
                              · rcases p24953_3 (m.d 1 3) (by simp) with h24982 | h24982
                                · rcases p24953_3 (m.d 2 3) (by simp) with h24983 | h24983
                                  · linarith only [h24983, hlam, p24953_0]
                                  · rcases p24953_3 (m.d 3 4) (by simp) with h24985 | h24985
                                    · rcases p24953_3 (m.d 3 5) (by simp) with h24986 | h24986
                                      · linarith only [h24874, h24986, hlam]
                                      · linarith only [h23731, h24986, hlam]
                                    · linarith only [h24985, hlam, p24953_0]
                                · linarith only [h22356, h24982, hlam]
                              · linarith only [h22350, h24981, hlam]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22362, h24024, h24874, hc23, hc34, hlam, hphi, p24953_1]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22354, hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22360, hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h22353, h22354, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24875_1, p24953_1]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [h24874, hlam, p24953_0]
                            · have p24953_0 := h24953c.1
                              have p24953_1 := h24953c.2.1
                              have p24953_2 := h24953c.2.2.1
                              have p24953_3 := h24953c.2.2.2
                              linarith only [hlam, p24953_0]
                    · linarith only [h22358, h24946, hlam]
                  · linarith only [h24945, hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h22350, h22353, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p24875_1, p24940_1]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h0, h22350, h22353, h22355, h22362, h24024, hlam, p24875_1, p24940_2]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h0, h22350, h22353, h22355, h24024, hlam, p24875_1, p24940_2]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  rcases p24940_3 (m.d 0 2) (by simp) with h25005 | h25005
                  · linarith only [h0, h25005, hlam]
                  · linarith only [h22352, h25005, hlam]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h22350, hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h22356, hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h22362, hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h23731, hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h22351, hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h22357, hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h0, h22350, h22353, h22354, h24024, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24875_1, p24940_1]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h24024, hlam, p24940_1]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h22352, hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h22358, hlam, p24940_0]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h0, h22350, h22352, h22353, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24875_1, p24940_1]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [h0, h22350, h22353, h22354, h24024, h24874, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p24875_1, p24940_1]
                · have p24940_0 := h24940c.1
                  have p24940_1 := h24940c.2.1
                  have p24940_2 := h24940c.2.2.1
                  have p24940_3 := h24940c.2.2.2
                  linarith only [hlam, p24940_0]
            · linarith only [h22355, h24937, hlam]
          · linarith only [h22354, h24936, hlam]
        · linarith only [h22352, h24935, hlam]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      rcases p24875_3 (m.d 0 1) (by simp) with h25026 | h25026
      · linarith only [h20697, h25026, hlam]
      · rcases p24875_3 (m.d 0 2) (by simp) with h25028 | h25028
        · rcases p24875_3 (m.d 0 3) (by simp) with h25029 | h25029
          · rcases p24875_3 (m.d 0 4) (by simp) with h25030 | h25030
            · rcases p24875_3 (m.d 0 5) (by simp) with h25031 | h25031
              · rcases h2bigk with h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c | h25032c
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h0, hlam, p25032_1]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h22350, h22353, h22362, h24024, h24874, hlam, p25032_2]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h22350, h22353, h24024, h24874, hlam, p25032_2]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  rcases p25032_3 (m.d 0 2) (by simp) with h25037 | h25037
                  · rcases p25032_3 (m.d 1 2) (by simp) with h25038 | h25038
                    · rcases p25032_3 (m.d 2 3) (by simp) with h25039 | h25039
                      · linarith only [h22350, h25039, hlam]
                      · rcases p25032_3 (m.d 2 4) (by simp) with h25041 | h25041
                        · linarith only [h22351, h25041, hlam]
                        · rcases p25032_3 (m.d 2 5) (by simp) with h25043 | h25043
                          · linarith only [h25043, hlam, p25032_0]
                          · rcases h3bigk with h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c | h25045c
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h15532, hlam, p25045_1]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h22353, h22362, h24024, h24874, hlam, p25045_2]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h0, h22350, h22362, h24024, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25045_1]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              rcases p25045_3 (m.d 0 3) (by simp) with h25050 | h25050
                              · rcases p25045_3 (m.d 1 3) (by simp) with h25051 | h25051
                                · rcases p25045_3 (m.d 2 3) (by simp) with h25052 | h25052
                                  · linarith only [h22350, h25052, hlam]
                                  · rcases p25045_3 (m.d 3 4) (by simp) with h25054 | h25054
                                    · linarith only [h22353, h25054, hlam]
                                    · linarith only [h24874, h25054, hlam]
                                · linarith only [h22360, h25051, hlam]
                              · linarith only [h25050, hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h22353, h22356, h22362, h24024, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25045_1]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h15532, h22353, h22362, h24024, h24874, hlam, p25045_2]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h22362, h24024, h24874, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25045_1]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              rcases p25045_3 (m.d 0 3) (by simp) with h25063 | h25063
                              · linarith only [h15532, h25063, hlam]
                              · linarith only [h22354, h25063, hlam]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h22350, hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h22356, hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h22362, hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h23731, hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h22353, hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h22359, hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              rcases p25045_3 (m.d 0 3) (by simp) with h25073 | h25073
                              · rcases p25045_3 (m.d 1 3) (by simp) with h25074 | h25074
                                · rcases p25045_3 (m.d 2 3) (by simp) with h25075 | h25075
                                  · linarith only [h25075, hlam, p25045_0]
                                  · rcases p25045_3 (m.d 3 4) (by simp) with h25077 | h25077
                                    · rcases p25045_3 (m.d 3 5) (by simp) with h25078 | h25078
                                      · linarith only [h24874, h25078, hlam]
                                      · linarith only [h23731, h25078, hlam]
                                    · linarith only [h25077, hlam, p25045_0]
                                · linarith only [h22356, h25074, hlam]
                              · linarith only [h22350, h25073, hlam]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h22353, h22362, h24024, h24874, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25045_1]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h22354, hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h22360, hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              rcases p25045_3 (m.d 0 3) (by simp) with h25088 | h25088
                              · rcases p25045_3 (m.d 1 3) (by simp) with h25089 | h25089
                                · rcases p25045_3 (m.d 2 3) (by simp) with h25090 | h25090
                                  · linarith only [h25090, hlam, p25045_0]
                                  · rcases p25045_3 (m.d 3 4) (by simp) with h25092 | h25092
                                    · rcases p25045_3 (m.d 3 5) (by simp) with h25093 | h25093
                                      · rcases h5bigk with h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c | h25094c
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [hlam, p25094_0]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h20697, hlam, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22352, hlam, p25032_2, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h20697, h22356, h22359, h22361, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25045_1, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h20697, h22356, h22359, h22361, h22362, h24024, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22356, h22359, h22361, hc01, hc12, hlam, hphi, p24875_1, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [hlam, p25094_0]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          rcases p25094_3 (m.d 0 5) (by simp) with h25102 | h25102
                                          · linarith only [h20697, h25102, hlam]
                                          · linarith only [h22352, h25102, hlam]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22356, h22359, h22361, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25045_1, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22356, h22359, h22361, h22362, h24024, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22352, hlam, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22358, hlam, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [hlam, p25094_0]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h23731, hlam, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h24024, hlam, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22354, hlam, p25094_0]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22360, hlam, p25094_0]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22350, h22353, h22362, h24024, h24874, hc23, hc35, hlam, hphi, p25032_2, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [hlam, p25094_0]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22350, h22353, h22362, h24024, h24874, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22355, hlam, p25094_0]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22361, hlam, p25094_0]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h22355, hc04, hc25, hlam, hphi, ht0b, ht5b, p25094_1]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [h24874, hlam, p25094_0]
                                        · have p25094_0 := h25094c.1
                                          have p25094_1 := h25094c.2.1
                                          have p25094_2 := h25094c.2.2.1
                                          have p25094_3 := h25094c.2.2.2
                                          linarith only [hlam, p25094_0]
                                      · linarith only [h25093, hlam, p25045_0]
                                    · linarith only [h22362, h25092, hlam]
                                · linarith only [h22356, h25089, hlam]
                              · linarith only [h22350, h25088, hlam]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [h24874, hlam, p25045_0]
                            · have p25045_0 := h25045c.1
                              have p25045_1 := h25045c.2.1
                              have p25045_2 := h25045c.2.2.1
                              have p25045_3 := h25045c.2.2.2
                              linarith only [hlam, p25045_0]
                    · linarith only [h22358, h25038, hlam]
                  · linarith only [h25037, hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h22352, hc01, hc12, hlam, hphi, p24875_1, p25032_1]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h0, h22350, h22353, h22362, h24024, h24874, hlam, p25032_2]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h0, h22350, h22353, h24024, h24874, hlam, p25032_2]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  rcases p25032_3 (m.d 0 2) (by simp) with h25134 | h25134
                  · linarith only [h0, h25134, hlam]
                  · linarith only [h22352, h25134, hlam]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h22350, hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h22356, hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h22362, hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h23731, hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h22351, hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h22357, hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h0, h22350, h22353, h24024, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25032_1]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h24024, hlam, p25032_1]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h22352, hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h22358, hlam, p25032_0]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h0, h22350, h22353, h24024, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25032_1]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [h0, h22350, h22353, h24024, h24874, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p25032_1]
                · have p25032_0 := h25032c.1
                  have p25032_1 := h25032c.2.1
                  have p25032_2 := h25032c.2.2.1
                  have p25032_3 := h25032c.2.2.2
                  linarith only [hlam, p25032_0]
              · linarith only [h20697, h25031, hlam]
            · linarith only [h18443, h25030, hlam]
          · linarith only [h15532, h25029, hlam]
        · linarith only [h0, h25028, hlam]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h22352, hlam, p24875_1]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h22354, hlam, p24875_0]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [h22355, hlam, p24875_1]
    · have p24875_0 := h24875c.1
      have p24875_1 := h24875c.2.1
      have p24875_2 := h24875c.2.2.1
      have p24875_3 := h24875c.2.2.2
      linarith only [hlam, p24875_0]
  · rcases h0bigk with h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c | h25160c
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [hlam, p25160_0]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h0, hlam, p25160_1]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h15532, hlam, p25160_0]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h18443, hlam, p25160_1]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h20697, hlam, p25160_1]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      rcases p25160_3 (m.d 0 1) (by simp) with h25166 | h25166
      · linarith only [h0, h25166, hlam]
      · rcases p25160_3 (m.d 0 2) (by simp) with h25168 | h25168
        · rcases p25160_3 (m.d 0 3) (by simp) with h25169 | h25169
          · linarith only [h22350, h25169, hlam]
          · linarith only [h15532, h25169, hlam]
        · linarith only [h0, h25168, hlam]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [hlam, p25160_0]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h0, h22353, h22362, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25160_1]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h0, h22355, h22362, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25160_1]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h0, h22355, h22362, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25160_1]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      rcases p25160_3 (m.d 0 1) (by simp) with h25177 | h25177
      · linarith only [h15532, h25177, hlam]
      · rcases p25160_3 (m.d 0 2) (by simp) with h25179 | h25179
        · rcases p25160_3 (m.d 0 3) (by simp) with h25180 | h25180
          · rcases p25160_3 (m.d 0 4) (by simp) with h25181 | h25181
            · linarith only [h22353, h25181, hlam]
            · linarith only [h18443, h25181, hlam]
          · linarith only [h15532, h25180, hlam]
        · linarith only [h0, h25179, hlam]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h22350, hlam, p25160_1]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [hlam, p25160_0]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h22355, h22362, h24874, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25160_1]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h15532, h22355, h22356, h22362, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25160_1]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      rcases p25160_3 (m.d 0 1) (by simp) with h25190 | h25190
      · linarith only [h18443, h25190, hlam]
      · rcases p25160_3 (m.d 0 2) (by simp) with h25192 | h25192
        · rcases p25160_3 (m.d 0 3) (by simp) with h25193 | h25193
          · rcases p25160_3 (m.d 0 4) (by simp) with h25194 | h25194
            · rcases p25160_3 (m.d 0 5) (by simp) with h25195 | h25195
              · linarith only [h22355, h25195, hlam]
              · linarith only [h20697, h25195, hlam]
            · linarith only [h18443, h25194, hlam]
          · linarith only [h15532, h25193, hlam]
        · linarith only [h0, h25192, hlam]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h22351, hlam, p25160_0]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h22353, hlam, p25160_0]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [hlam, p25160_0]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h22355, h22362, h24874, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25160_1]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      rcases p25160_3 (m.d 0 1) (by simp) with h25205 | h25205
      · linarith only [h20697, h25205, hlam]
      · rcases p25160_3 (m.d 0 2) (by simp) with h25207 | h25207
        · rcases p25160_3 (m.d 0 3) (by simp) with h25208 | h25208
          · rcases p25160_3 (m.d 0 4) (by simp) with h25209 | h25209
            · rcases p25160_3 (m.d 0 5) (by simp) with h25210 | h25210
              · rcases h2bigk with h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c | h25211c
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h0, hlam, p25211_1]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h22350, h22353, h22355, h22362, h24874, hlam, p25211_2]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  rcases p25211_3 (m.d 0 2) (by simp) with h25215 | h25215
                  · rcases p25211_3 (m.d 1 2) (by simp) with h25216 | h25216
                    · rcases p25211_3 (m.d 2 3) (by simp) with h25217 | h25217
                      · linarith only [h22350, h25217, hlam]
                      · rcases p25211_3 (m.d 2 4) (by simp) with h25219 | h25219
                        · linarith only [h25219, hlam, p25211_0]
                        · rcases p25211_3 (m.d 2 5) (by simp) with h25221 | h25221
                          · linarith only [h22352, h25221, hlam]
                          · linarith only [h24024, h25221, hlam]
                    · linarith only [h22357, h25216, hlam]
                  · linarith only [h25215, hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  rcases p25211_3 (m.d 0 2) (by simp) with h25226 | h25226
                  · rcases p25211_3 (m.d 1 2) (by simp) with h25227 | h25227
                    · rcases p25211_3 (m.d 2 3) (by simp) with h25228 | h25228
                      · linarith only [h22350, h25228, hlam]
                      · rcases p25211_3 (m.d 2 4) (by simp) with h25230 | h25230
                        · linarith only [h22351, h25230, hlam]
                        · rcases p25211_3 (m.d 2 5) (by simp) with h25232 | h25232
                          · linarith only [h25232, hlam, p25211_0]
                          · rcases h3bigk with h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c | h25234c
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h15532, hlam, p25234_1]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h22353, h22355, h22362, h24874, hlam, p25234_2]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              rcases p25234_3 (m.d 0 3) (by simp) with h25238 | h25238
                              · rcases p25234_3 (m.d 1 3) (by simp) with h25239 | h25239
                                · rcases p25234_3 (m.d 2 3) (by simp) with h25240 | h25240
                                  · linarith only [h22350, h25240, hlam]
                                  · rcases p25234_3 (m.d 3 4) (by simp) with h25242 | h25242
                                    · linarith only [h25242, hlam, p25234_0]
                                    · rcases p25234_3 (m.d 3 5) (by simp) with h25244 | h25244
                                      · linarith only [h22354, h25244, hlam]
                                      · linarith only [h24874, h25244, hlam]
                                · linarith only [h22359, h25239, hlam]
                              · linarith only [h25238, hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              rcases p25234_3 (m.d 0 3) (by simp) with h25249 | h25249
                              · rcases p25234_3 (m.d 1 3) (by simp) with h25250 | h25250
                                · rcases p25234_3 (m.d 2 3) (by simp) with h25251 | h25251
                                  · linarith only [h22350, h25251, hlam]
                                  · rcases p25234_3 (m.d 3 4) (by simp) with h25253 | h25253
                                    · linarith only [h22353, h25253, hlam]
                                    · rcases p25234_3 (m.d 3 5) (by simp) with h25255 | h25255
                                      · linarith only [h25255, hlam, p25234_0]
                                      · rcases h5bigk with h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c | h25257c
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [hlam, p25257_0]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h20697, hlam, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22352, hlam, p25211_2, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22354, hlam, p25234_2, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22350, h22353, h22355, h22362, h24874, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22356, h22359, h22361, hc01, hc12, hlam, hphi, p25160_1, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [hlam, p25257_0]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          rcases p25257_3 (m.d 0 5) (by simp) with h25265 | h25265
                                          · linarith only [h20697, h25265, hlam]
                                          · linarith only [h22352, h25265, hlam]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22356, h22359, h22361, h22362, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22356, h22359, h22361, h22362, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22352, hlam, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22358, hlam, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [hlam, p25257_0]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h23731, hlam, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h24024, hlam, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22354, hlam, p25257_0]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22360, hlam, p25257_0]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22350, hlam, p25211_2, p25234_1, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [hlam, p25257_0]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h24874, hlam, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22355, hlam, p25257_0]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22361, hlam, p25257_0]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h24024, hc24, hc45, hlam, hphi, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [h22350, h22353, h22355, hc02, hc35, hlam, hphi, ht0b, ht5b, p25257_1]
                                        · have p25257_0 := h25257c.1
                                          have p25257_1 := h25257c.2.1
                                          have p25257_2 := h25257c.2.2.1
                                          have p25257_3 := h25257c.2.2.2
                                          linarith only [hlam, p25257_0]
                                · linarith only [h22360, h25250, hlam]
                              · linarith only [h25249, hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h22353, h22355, h22356, h22362, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25234_1]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h15532, h22353, h22355, h22362, h24874, hlam, p25234_2]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              rcases p25234_3 (m.d 0 3) (by simp) with h25290 | h25290
                              · linarith only [h15532, h25290, hlam]
                              · linarith only [h22353, h25290, hlam]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              rcases p25234_3 (m.d 0 3) (by simp) with h25293 | h25293
                              · linarith only [h15532, h25293, hlam]
                              · linarith only [h22354, h25293, hlam]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h22350, hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h22356, hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h22362, hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h23731, hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h22353, hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h22359, hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h22353, h22355, h24874, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25234_1]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h24874, hlam, p25234_1]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h22354, hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h22360, hlam, p25234_0]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              rcases p25234_3 (m.d 0 3) (by simp) with h25308 | h25308
                              · rcases p25234_3 (m.d 1 3) (by simp) with h25309 | h25309
                                · rcases p25234_3 (m.d 2 3) (by simp) with h25310 | h25310
                                  · linarith only [h25310, hlam, p25234_0]
                                  · rcases p25234_3 (m.d 3 4) (by simp) with h25312 | h25312
                                    · linarith only [h24874, h25312, hlam]
                                    · linarith only [h22362, h25312, hlam]
                                · linarith only [h22356, h25309, hlam]
                              · linarith only [h22350, h25308, hlam]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [h0, h22350, h22354, h22362, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25234_1]
                            · have p25234_0 := h25234c.1
                              have p25234_1 := h25234c.2.1
                              have p25234_2 := h25234c.2.2.1
                              have p25234_3 := h25234c.2.2.2
                              linarith only [hlam, p25234_0]
                    · linarith only [h22358, h25227, hlam]
                  · linarith only [h25226, hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h22352, hc01, hc12, hlam, hphi, p25160_1, p25211_1]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h0, h22350, h22353, h22355, h22362, h24874, hlam, p25211_2]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  rcases p25211_3 (m.d 0 2) (by simp) with h25324 | h25324
                  · linarith only [h0, h25324, hlam]
                  · linarith only [h22351, h25324, hlam]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  rcases p25211_3 (m.d 0 2) (by simp) with h25327 | h25327
                  · linarith only [h0, h25327, hlam]
                  · linarith only [h22352, h25327, hlam]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h22350, hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h22356, hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h22362, hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h23731, hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h22351, hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h22357, hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h0, h22350, h22353, h22355, h22362, h24874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25211_1]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h24024, hlam, p25211_1]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h22352, hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [h22358, hlam, p25211_0]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  rcases p25211_3 (m.d 0 2) (by simp) with h25342 | h25342
                  · rcases p25211_3 (m.d 1 2) (by simp) with h25343 | h25343
                    · rcases p25211_3 (m.d 2 3) (by simp) with h25344 | h25344
                      · linarith only [h23731, h25344, hlam]
                      · rcases p25211_3 (m.d 2 4) (by simp) with h25346 | h25346
                        · linarith only [h24024, h25346, hlam]
                        · linarith only [h22362, h25346, hlam]
                    · linarith only [h22356, h25343, hlam]
                  · linarith only [h22350, h25342, hlam]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  rcases p25211_3 (m.d 0 2) (by simp) with h25351 | h25351
                  · rcases p25211_3 (m.d 1 2) (by simp) with h25352 | h25352
                    · rcases p25211_3 (m.d 2 3) (by simp) with h25353 | h25353
                      · linarith only [h23731, h25353, hlam]
                      · rcases p25211_3 (m.d 2 4) (by simp) with h25355 | h25355
                        · linarith only [h24024, h25355, hlam]
                        · rcases p25211_3 (m.d 2 5) (by simp) with h25357 | h25357
                          · rcases h3bigk with h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c | h25358c
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h15532, hlam, p25358_1]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h22353, h22355, h22362, h24874, hlam, p25358_2]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              rcases p25358_3 (m.d 0 3) (by simp) with h25362 | h25362
                              · rcases p25358_3 (m.d 1 3) (by simp) with h25363 | h25363
                                · rcases p25358_3 (m.d 2 3) (by simp) with h25364 | h25364
                                  · linarith only [h22350, h25364, hlam]
                                  · rcases p25358_3 (m.d 3 4) (by simp) with h25366 | h25366
                                    · linarith only [h25366, hlam, p25358_0]
                                    · rcases p25358_3 (m.d 3 5) (by simp) with h25368 | h25368
                                      · linarith only [h22354, h25368, hlam]
                                      · linarith only [h24874, h25368, hlam]
                                · linarith only [h22359, h25363, hlam]
                              · linarith only [h25362, hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h15532, h22356, h22362, h23731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25211_1, p25358_1]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h22353, h22355, h22356, h24874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p25358_1]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h15532, h22354, h22362, h23731, hlam, p25211_1, p25358_2]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              rcases p25358_3 (m.d 0 3) (by simp) with h25377 | h25377
                              · linarith only [h15532, h25377, hlam]
                              · linarith only [h22353, h25377, hlam]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h22362, h23731, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25211_1, p25358_1]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h22350, hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h22356, hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h22362, hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h23731, hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h22353, hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h22359, hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h22353, h22355, h24874, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25358_1]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h24874, hlam, p25358_1]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h22354, hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h22360, hlam, p25358_0]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              rcases p25358_3 (m.d 0 3) (by simp) with h25393 | h25393
                              · rcases p25358_3 (m.d 1 3) (by simp) with h25394 | h25394
                                · rcases p25358_3 (m.d 2 3) (by simp) with h25395 | h25395
                                  · linarith only [h25395, hlam, p25358_0]
                                  · rcases p25358_3 (m.d 3 4) (by simp) with h25397 | h25397
                                    · linarith only [h24874, h25397, hlam]
                                    · linarith only [h22362, h25397, hlam]
                                · linarith only [h22356, h25394, hlam]
                              · linarith only [h22350, h25393, hlam]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [h15532, h22354, h22356, h22362, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25358_1]
                            · have p25358_0 := h25358c.1
                              have p25358_1 := h25358c.2.1
                              have p25358_2 := h25358c.2.2.1
                              have p25358_3 := h25358c.2.2.2
                              linarith only [hlam, p25358_0]
                          · linarith only [h24024, h25357, hlam]
                    · linarith only [h22357, h25352, hlam]
                  · linarith only [h22351, h25351, hlam]
                · have p25211_0 := h25211c.1
                  have p25211_1 := h25211c.2.1
                  have p25211_2 := h25211c.2.2.1
                  have p25211_3 := h25211c.2.2.2
                  linarith only [hlam, p25211_0]
              · linarith only [h20697, h25210, hlam]
            · linarith only [h18443, h25209, hlam]
          · linarith only [h15532, h25208, hlam]
        · linarith only [h0, h25207, hlam]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h22352, hlam, p25160_1]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h22354, hlam, p25160_0]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [h22355, hlam, p25160_1]
    · have p25160_0 := h25160c.1
      have p25160_1 := h25160c.2.1
      have p25160_2 := h25160c.2.2.1
      have p25160_3 := h25160c.2.2.2
      linarith only [hlam, p25160_0]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1 (m : N7Model)
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
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  rcases m.htr 2 4 5 (by decide) (by decide) with h24024 | h24024
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1 (m : N7Model)
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
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h23731 | h23731
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32 (m : N7Model)
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
  rcases m.htr 2 3 4 (by decide) (by decide) with h22362 | h22362
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362

set_option maxHeartbeats 6112000 in
set_option maxHeartbeats 6112000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s31 (m : N7Model)
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
  rcases m.htr 1 4 5 (by decide) (by decide) with h22361 | h22361
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697 h22350 h22351 h22352 h22353 h22354 h22355 h22356 h22357 h22358 h22359 h22360 h22361
  · linarith only [h15532, h18443, h22353, h22355, h22356, h22361, hc01, hc12, hlam, hphi]

set_option maxHeartbeats 6116000 in
set_option maxHeartbeats 6116000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s30 (m : N7Model)
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
  rcases m.htr 1 3 5 (by decide) (by decide) with h22360 | h22360
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s31 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697 h22350 h22351 h22352 h22353 h22354 h22355 h22356 h22357 h22358 h22359 h22360
  · linarith only [h15532, h22354, h22360, hlam]

set_option maxHeartbeats 6120000 in
set_option maxHeartbeats 6120000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s29 (m : N7Model)
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
  rcases m.htr 1 3 4 (by decide) (by decide) with h22359 | h22359
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s30 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697 h22350 h22351 h22352 h22353 h22354 h22355 h22356 h22357 h22358 h22359
  · linarith only [h15532, h22353, h22359, hlam]

set_option maxHeartbeats 6124000 in
set_option maxHeartbeats 6124000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s28 (m : N7Model)
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h22358 | h22358
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s29 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697 h22350 h22351 h22352 h22353 h22354 h22355 h22356 h22357 h22358
  · linarith only [h0, h22352, h22358, hlam]

set_option maxHeartbeats 6128000 in
set_option maxHeartbeats 6128000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s27 (m : N7Model)
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h22357 | h22357
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s28 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697 h22350 h22351 h22352 h22353 h22354 h22355 h22356 h22357
  · linarith only [h0, h22351, h22357, hlam]

set_option maxHeartbeats 6132000 in
set_option maxHeartbeats 6132000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s26 (m : N7Model)
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h22356 | h22356
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s27 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697 h22350 h22351 h22352 h22353 h22354 h22355 h22356
  · linarith only [h0, h22350, h22356, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x0 (m : N7Model)
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
    (h22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h22353 := hg22353
  have h22354 := hg22354
  exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s26 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697 h22350 h22351 h22352 h22353 h22354 h22355

end R2N4
