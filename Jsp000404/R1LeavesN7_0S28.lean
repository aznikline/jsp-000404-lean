import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h15885 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h15893 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h15899 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h15901 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h15903 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 2 3 4 (by decide) (by decide) with h15904 | h15904
  · linarith only [h15904, h4, h7, hlam]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h15906 | h15906
    · linarith only [h13284, h15906, h4, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h15908 | h15908
      · rcases m.htr 3 4 5 (by decide) (by decide) with h15909 | h15909
        · rcases h1bigk with h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c | h15910c
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            rcases p15910_3 (m.d 0 1) (by simp) with h15912 | h15912
            · rcases p15910_3 (m.d 1 2) (by simp) with h15913 | h15913
              · linarith only [h15913, hlam, p15910_0]
              · rcases p15910_3 (m.d 1 3) (by simp) with h15915 | h15915
                · linarith only [h1, h15915, hlam]
                · linarith only [h14160, h15915, hlam]
            · linarith only [h15912, hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            rcases p15910_3 (m.d 0 1) (by simp) with h15919 | h15919
            · rcases p15910_3 (m.d 1 2) (by simp) with h15920 | h15920
              · linarith only [h0, h15920, hlam]
              · rcases p15910_3 (m.d 1 3) (by simp) with h15922 | h15922
                · linarith only [h15922, hlam, p15910_0]
                · rcases p15910_3 (m.d 1 4) (by simp) with h15924 | h15924
                  · linarith only [h15924, h2, hlam]
                  · linarith only [h15899, h15924, hlam]
            · linarith only [h15919, hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            rcases p15910_3 (m.d 0 1) (by simp) with h15928 | h15928
            · rcases p15910_3 (m.d 1 2) (by simp) with h15929 | h15929
              · linarith only [h0, h15929, hlam]
              · rcases p15910_3 (m.d 1 3) (by simp) with h15931 | h15931
                · linarith only [h1, h15931, hlam]
                · rcases p15910_3 (m.d 1 4) (by simp) with h15933 | h15933
                  · linarith only [h15933, hlam, p15910_0]
                  · rcases p15910_3 (m.d 1 5) (by simp) with h15935 | h15935
                    · linarith only [h15935, h3, hlam]
                    · rcases h1emax with h15937 | h15937 | h15937 | h15937 | h15937
                      · linarith only [h15901, h15903, h15937, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15910_1]
                      · rcases h2bigk with h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c | h15939c
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          rcases p15939_3 (m.d 0 2) (by simp) with h15941 | h15941
                          · rcases p15939_3 (m.d 1 2) (by simp) with h15942 | h15942
                            · linarith only [h0, h15942, hlam]
                            · rcases p15939_3 (m.d 2 3) (by simp) with h15944 | h15944
                              · linarith only [h15944, h4, hlam]
                              · linarith only [h14160, h15944, hlam]
                          · linarith only [h0, h15941, hlam]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          rcases p15939_3 (m.d 0 2) (by simp) with h15948 | h15948
                          · rcases p15939_3 (m.d 1 2) (by simp) with h15949 | h15949
                            · linarith only [h0, h15949, hlam]
                            · rcases p15939_3 (m.d 2 3) (by simp) with h15951 | h15951
                              · linarith only [h15951, hlam, p15939_0]
                              · rcases p15939_3 (m.d 2 4) (by simp) with h15953 | h15953
                                · linarith only [h15953, h5, hlam]
                                · linarith only [h15904, h15953, hlam]
                          · linarith only [h15948, hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          rcases p15939_3 (m.d 0 2) (by simp) with h15957 | h15957
                          · rcases p15939_3 (m.d 1 2) (by simp) with h15958 | h15958
                            · linarith only [h0, h15958, hlam]
                            · rcases p15939_3 (m.d 2 3) (by simp) with h15960 | h15960
                              · linarith only [h15960, h4, hlam]
                              · rcases p15939_3 (m.d 2 4) (by simp) with h15962 | h15962
                                · linarith only [h15962, hlam, p15939_0]
                                · rcases p15939_3 (m.d 2 5) (by simp) with h15964 | h15964
                                  · linarith only [h15964, h6, hlam]
                                  · rcases h4bigk with h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c | h15966c
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [hlam, p15966_0]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      rcases p15966_3 (m.d 0 4) (by simp) with h15968 | h15968
                                      · rcases p15966_3 (m.d 1 4) (by simp) with h15969 | h15969
                                        · linarith only [h15969, h2, hlam]
                                        · rcases p15966_3 (m.d 2 4) (by simp) with h15971 | h15971
                                          · linarith only [h15971, h5, hlam]
                                          · linarith only [h15885, h15971, hlam]
                                      · linarith only [h15968, h2, hlam]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h14160, h15906, h15908, h7, hc12, hc34, hlam, hphi, ht23, p15966_1]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h7, hlam, p15966_1]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      rcases p15966_3 (m.d 0 4) (by simp) with h15977 | h15977
                                      · rcases p15966_3 (m.d 1 4) (by simp) with h15978 | h15978
                                        · linarith only [h15978, h2, hlam]
                                        · linarith only [h15903, h15978, hlam]
                                      · linarith only [h15977, hlam, p15966_0]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h2, hlam, p15966_0]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [hlam, p15966_0]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h15885, hlam, p15966_1]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h15899, hlam, p15966_1]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p15910_1, p15966_1]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h5, hlam, p15966_0]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p15939_1, p15966_1]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [hlam, p15966_0]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h15904, hlam, p15966_1]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p15939_1, p15966_1]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h14160, h15906, h15908, h5, hc12, hc34, hlam, hphi, ht23, p15966_1]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      rcases p15966_3 (m.d 0 4) (by simp) with h15993 | h15993
                                      · linarith only [h15993, h7, hlam]
                                      · linarith only [h15993, h2, hlam]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h14160, h15906, h15908, hc12, hc34, hlam, hphi, ht23, p15966_1]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [hlam, p15966_0]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      rcases p15966_3 (m.d 0 4) (by simp) with h15998 | h15998
                                      · linarith only [h15998, h7, hlam]
                                      · linarith only [h14159, h15998, hlam]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h14159, hlam, p15966_0]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h15903, hlam, p15966_0]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h15908, hlam, p15966_0]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [h15909, hlam, p15966_0]
                                    · have p15966_0 := h15966c.1
                                      have p15966_1 := h15966c.2.1
                                      have p15966_2 := h15966c.2.2.1
                                      have p15966_3 := h15966c.2.2.2
                                      linarith only [hlam, p15966_0]
                          · linarith only [h15957, hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          rcases p15939_3 (m.d 0 2) (by simp) with h16007 | h16007
                          · rcases p15939_3 (m.d 1 2) (by simp) with h16008 | h16008
                            · linarith only [h0, h16008, hlam]
                            · rcases p15939_3 (m.d 2 3) (by simp) with h16010 | h16010
                              · linarith only [h16010, h4, hlam]
                              · rcases p15939_3 (m.d 2 4) (by simp) with h16012 | h16012
                                · linarith only [h16012, h5, hlam]
                                · linarith only [h15908, h16012, hlam]
                          · linarith only [h16007, hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h0, hlam, p15939_1]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h14160, hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h15885, hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h15893, hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h4, hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h13284, h4, hc12, hc35, hlam, hphi, ht23, p15939_1]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h15904, hlam, p15939_1]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h15906, hlam, p15939_1]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h5, hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          rcases p15939_3 (m.d 0 2) (by simp) with h16027 | h16027
                          · rcases p15939_3 (m.d 1 2) (by simp) with h16028 | h16028
                            · linarith only [h16028, hlam, p15939_0]
                            · rcases p15939_3 (m.d 2 3) (by simp) with h16030 | h16030
                              · linarith only [h15904, h16030, hlam]
                              · linarith only [h14160, h16030, hlam]
                          · linarith only [h0, h16027, hlam]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h14160, hc12, hc24, hlam, hphi, p15939_1]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h0, h14160, h15906, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15939_1]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h6, hlam, p15939_0]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          rcases p15939_3 (m.d 0 2) (by simp) with h16038 | h16038
                          · rcases p15939_3 (m.d 1 2) (by simp) with h16039 | h16039
                            · linarith only [h16039, hlam, p15939_0]
                            · rcases p15939_3 (m.d 2 3) (by simp) with h16041 | h16041
                              · linarith only [h15906, h16041, hlam]
                              · linarith only [h14160, h16041, hlam]
                          · linarith only [h0, h16038, hlam]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p15939_1]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [h15908, hlam, p15939_1]
                        · have p15939_0 := h15939c.1
                          have p15939_1 := h15939c.2.1
                          have p15939_2 := h15939c.2.2.1
                          have p15939_3 := h15939c.2.2.2
                          linarith only [hlam, p15939_0]
                      · rcases h2bigk with h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          rcases p16048_3 (m.d 0 2) (by simp) with h16050 | h16050
                          · rcases p16048_3 (m.d 1 2) (by simp) with h16051 | h16051
                            · linarith only [h0, h16051, hlam]
                            · rcases p16048_3 (m.d 2 3) (by simp) with h16053 | h16053
                              · linarith only [h16053, h4, hlam]
                              · linarith only [h14160, h16053, hlam]
                          · linarith only [h0, h16050, hlam]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          rcases p16048_3 (m.d 0 2) (by simp) with h16057 | h16057
                          · rcases p16048_3 (m.d 1 2) (by simp) with h16058 | h16058
                            · linarith only [h0, h16058, hlam]
                            · rcases p16048_3 (m.d 2 3) (by simp) with h16060 | h16060
                              · linarith only [h16060, hlam, p16048_0]
                              · rcases p16048_3 (m.d 2 4) (by simp) with h16062 | h16062
                                · linarith only [h16062, h5, hlam]
                                · linarith only [h15904, h16062, hlam]
                          · linarith only [h16057, hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          rcases p16048_3 (m.d 0 2) (by simp) with h16066 | h16066
                          · rcases p16048_3 (m.d 1 2) (by simp) with h16067 | h16067
                            · linarith only [h0, h16067, hlam]
                            · rcases p16048_3 (m.d 2 3) (by simp) with h16069 | h16069
                              · linarith only [h16069, h4, hlam]
                              · rcases p16048_3 (m.d 2 4) (by simp) with h16071 | h16071
                                · linarith only [h16071, hlam, p16048_0]
                                · rcases p16048_3 (m.d 2 5) (by simp) with h16073 | h16073
                                  · linarith only [h16073, h6, hlam]
                                  · rcases h4bigk with h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [hlam, p16075_0]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      rcases p16075_3 (m.d 0 4) (by simp) with h16077 | h16077
                                      · rcases p16075_3 (m.d 1 4) (by simp) with h16078 | h16078
                                        · linarith only [h16078, h2, hlam]
                                        · rcases p16075_3 (m.d 2 4) (by simp) with h16080 | h16080
                                          · linarith only [h16080, h5, hlam]
                                          · linarith only [h15885, h16080, hlam]
                                      · linarith only [h16077, h2, hlam]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h14160, h15906, h15908, h7, hc12, hc34, hlam, hphi, ht23, p16075_1]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h7, hlam, p16075_1]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      rcases p16075_3 (m.d 0 4) (by simp) with h16086 | h16086
                                      · rcases p16075_3 (m.d 1 4) (by simp) with h16087 | h16087
                                        · linarith only [h16087, h2, hlam]
                                        · linarith only [h15903, h16087, hlam]
                                      · linarith only [h16086, hlam, p16075_0]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h2, hlam, p16075_0]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [hlam, p16075_0]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h15885, hlam, p16075_1]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h15899, hlam, p16075_1]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p15910_1, p16075_1]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h5, hlam, p16075_0]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p16048_1, p16075_1]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [hlam, p16075_0]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h15904, hlam, p16075_1]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p16048_1, p16075_1]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h14160, h15906, h15908, h5, hc12, hc34, hlam, hphi, ht23, p16075_1]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      rcases p16075_3 (m.d 0 4) (by simp) with h16102 | h16102
                                      · linarith only [h16102, h7, hlam]
                                      · linarith only [h16102, h2, hlam]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h14160, h15906, h15908, hc12, hc34, hlam, hphi, ht23, p16075_1]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [hlam, p16075_0]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      rcases p16075_3 (m.d 0 4) (by simp) with h16107 | h16107
                                      · linarith only [h16107, h7, hlam]
                                      · linarith only [h14159, h16107, hlam]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h14159, hlam, p16075_0]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h15903, hlam, p16075_0]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h15908, hlam, p16075_0]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [h15909, hlam, p16075_0]
                                    · have p16075_0 := h16075c.1
                                      have p16075_1 := h16075c.2.1
                                      have p16075_2 := h16075c.2.2.1
                                      have p16075_3 := h16075c.2.2.2
                                      linarith only [hlam, p16075_0]
                          · linarith only [h16066, hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          rcases p16048_3 (m.d 0 2) (by simp) with h16116 | h16116
                          · rcases p16048_3 (m.d 1 2) (by simp) with h16117 | h16117
                            · linarith only [h0, h16117, hlam]
                            · rcases p16048_3 (m.d 2 3) (by simp) with h16119 | h16119
                              · linarith only [h16119, h4, hlam]
                              · rcases p16048_3 (m.d 2 4) (by simp) with h16121 | h16121
                                · linarith only [h16121, h5, hlam]
                                · linarith only [h15908, h16121, hlam]
                          · linarith only [h16116, hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h0, hlam, p16048_1]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h14160, hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h15885, hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h15893, hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h4, hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h13284, h15909, h4, hc12, hc34, hlam, hphi, ht23, p16048_1]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h15904, hlam, p16048_1]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h15906, hlam, p16048_1]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h5, hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          rcases p16048_3 (m.d 0 2) (by simp) with h16136 | h16136
                          · rcases p16048_3 (m.d 1 2) (by simp) with h16137 | h16137
                            · linarith only [h16137, hlam, p16048_0]
                            · rcases p16048_3 (m.d 2 3) (by simp) with h16139 | h16139
                              · linarith only [h15904, h16139, hlam]
                              · linarith only [h14160, h16139, hlam]
                          · linarith only [h0, h16136, hlam]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h0, h14160, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16048_1]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h0, h14160, h15906, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16048_1]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h6, hlam, p16048_0]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          rcases p16048_3 (m.d 0 2) (by simp) with h16147 | h16147
                          · rcases p16048_3 (m.d 1 2) (by simp) with h16148 | h16148
                            · linarith only [h16148, hlam, p16048_0]
                            · rcases p16048_3 (m.d 2 3) (by simp) with h16150 | h16150
                              · linarith only [h15906, h16150, hlam]
                              · linarith only [h14160, h16150, hlam]
                          · linarith only [h0, h16147, hlam]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p16048_1]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [h15908, hlam, p16048_1]
                        · have p16048_0 := h16048c.1
                          have p16048_1 := h16048c.2.1
                          have p16048_2 := h16048c.2.2.1
                          have p16048_3 := h16048c.2.2.2
                          linarith only [hlam, p16048_0]
                      · rcases h2bigk with h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c | h16157c
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          rcases p16157_3 (m.d 0 2) (by simp) with h16159 | h16159
                          · rcases p16157_3 (m.d 1 2) (by simp) with h16160 | h16160
                            · linarith only [h0, h16160, hlam]
                            · rcases p16157_3 (m.d 2 3) (by simp) with h16162 | h16162
                              · linarith only [h16162, h4, hlam]
                              · linarith only [h14160, h16162, hlam]
                          · linarith only [h0, h16159, hlam]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          rcases p16157_3 (m.d 0 2) (by simp) with h16166 | h16166
                          · rcases p16157_3 (m.d 1 2) (by simp) with h16167 | h16167
                            · linarith only [h0, h16167, hlam]
                            · rcases p16157_3 (m.d 2 3) (by simp) with h16169 | h16169
                              · linarith only [h16169, hlam, p16157_0]
                              · rcases p16157_3 (m.d 2 4) (by simp) with h16171 | h16171
                                · linarith only [h16171, h5, hlam]
                                · linarith only [h15904, h16171, hlam]
                          · linarith only [h16166, hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          rcases p16157_3 (m.d 0 2) (by simp) with h16175 | h16175
                          · rcases p16157_3 (m.d 1 2) (by simp) with h16176 | h16176
                            · linarith only [h0, h16176, hlam]
                            · rcases p16157_3 (m.d 2 3) (by simp) with h16178 | h16178
                              · linarith only [h16178, h4, hlam]
                              · rcases p16157_3 (m.d 2 4) (by simp) with h16180 | h16180
                                · linarith only [h16180, hlam, p16157_0]
                                · rcases p16157_3 (m.d 2 5) (by simp) with h16182 | h16182
                                  · linarith only [h16182, h6, hlam]
                                  · rcases h4bigk with h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c | h16184c
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [hlam, p16184_0]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      rcases p16184_3 (m.d 0 4) (by simp) with h16186 | h16186
                                      · rcases p16184_3 (m.d 1 4) (by simp) with h16187 | h16187
                                        · linarith only [h16187, h2, hlam]
                                        · rcases p16184_3 (m.d 2 4) (by simp) with h16189 | h16189
                                          · linarith only [h16189, h5, hlam]
                                          · linarith only [h15885, h16189, hlam]
                                      · linarith only [h16186, h2, hlam]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h14160, h15906, h15908, h7, hc12, hc34, hlam, hphi, ht23, p16184_1]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h7, hlam, p16184_1]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      rcases p16184_3 (m.d 0 4) (by simp) with h16195 | h16195
                                      · rcases p16184_3 (m.d 1 4) (by simp) with h16196 | h16196
                                        · linarith only [h16196, h2, hlam]
                                        · linarith only [h15903, h16196, hlam]
                                      · linarith only [h16195, hlam, p16184_0]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h2, hlam, p16184_0]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [hlam, p16184_0]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h15885, hlam, p16184_1]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h15899, hlam, p16184_1]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p15910_1, p16184_1]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h5, hlam, p16184_0]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p16157_1, p16184_1]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [hlam, p16184_0]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h15904, hlam, p16184_1]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p16157_1, p16184_1]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h14160, h15906, h15908, h5, hc12, hc34, hlam, hphi, ht23, p16184_1]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      rcases p16184_3 (m.d 0 4) (by simp) with h16211 | h16211
                                      · linarith only [h16211, h7, hlam]
                                      · linarith only [h16211, h2, hlam]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h14160, h15906, h15908, hc12, hc34, hlam, hphi, ht23, p16184_1]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [hlam, p16184_0]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      rcases p16184_3 (m.d 0 4) (by simp) with h16216 | h16216
                                      · linarith only [h16216, h7, hlam]
                                      · linarith only [h14159, h16216, hlam]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h14159, hlam, p16184_0]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h15903, hlam, p16184_0]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h15908, hlam, p16184_0]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [h15909, hlam, p16184_0]
                                    · have p16184_0 := h16184c.1
                                      have p16184_1 := h16184c.2.1
                                      have p16184_2 := h16184c.2.2.1
                                      have p16184_3 := h16184c.2.2.2
                                      linarith only [hlam, p16184_0]
                          · linarith only [h16175, hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          rcases p16157_3 (m.d 0 2) (by simp) with h16225 | h16225
                          · rcases p16157_3 (m.d 1 2) (by simp) with h16226 | h16226
                            · linarith only [h0, h16226, hlam]
                            · rcases p16157_3 (m.d 2 3) (by simp) with h16228 | h16228
                              · linarith only [h16228, h4, hlam]
                              · rcases p16157_3 (m.d 2 4) (by simp) with h16230 | h16230
                                · linarith only [h16230, h5, hlam]
                                · linarith only [h15908, h16230, hlam]
                          · linarith only [h16225, hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h0, hlam, p16157_1]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h14160, hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h15885, hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h15893, hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h4, hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p16157_1]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h15904, hlam, p16157_1]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h15906, hlam, p16157_1]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h5, hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          rcases p16157_3 (m.d 0 2) (by simp) with h16245 | h16245
                          · rcases p16157_3 (m.d 1 2) (by simp) with h16246 | h16246
                            · linarith only [h16246, hlam, p16157_0]
                            · rcases p16157_3 (m.d 2 3) (by simp) with h16248 | h16248
                              · linarith only [h15904, h16248, hlam]
                              · linarith only [h14160, h16248, hlam]
                          · linarith only [h0, h16245, hlam]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h0, h14160, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16157_1]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h0, h14160, h15906, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16157_1]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h6, hlam, p16157_0]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          rcases p16157_3 (m.d 0 2) (by simp) with h16256 | h16256
                          · rcases p16157_3 (m.d 1 2) (by simp) with h16257 | h16257
                            · linarith only [h16257, hlam, p16157_0]
                            · rcases p16157_3 (m.d 2 3) (by simp) with h16259 | h16259
                              · linarith only [h15906, h16259, hlam]
                              · linarith only [h14160, h16259, hlam]
                          · linarith only [h0, h16256, hlam]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p16157_1]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [h15908, hlam, p16157_1]
                        · have p16157_0 := h16157c.1
                          have p16157_1 := h16157c.2.1
                          have p16157_2 := h16157c.2.2.1
                          have p16157_3 := h16157c.2.2.2
                          linarith only [hlam, p16157_0]
                      · rcases h2bigk with h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c | h16266c
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          rcases p16266_3 (m.d 0 2) (by simp) with h16268 | h16268
                          · rcases p16266_3 (m.d 1 2) (by simp) with h16269 | h16269
                            · linarith only [h0, h16269, hlam]
                            · rcases p16266_3 (m.d 2 3) (by simp) with h16271 | h16271
                              · linarith only [h16271, h4, hlam]
                              · linarith only [h14160, h16271, hlam]
                          · linarith only [h0, h16268, hlam]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          rcases p16266_3 (m.d 0 2) (by simp) with h16275 | h16275
                          · rcases p16266_3 (m.d 1 2) (by simp) with h16276 | h16276
                            · linarith only [h0, h16276, hlam]
                            · rcases p16266_3 (m.d 2 3) (by simp) with h16278 | h16278
                              · linarith only [h16278, hlam, p16266_0]
                              · rcases p16266_3 (m.d 2 4) (by simp) with h16280 | h16280
                                · linarith only [h16280, h5, hlam]
                                · linarith only [h15904, h16280, hlam]
                          · linarith only [h16275, hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          rcases p16266_3 (m.d 0 2) (by simp) with h16284 | h16284
                          · rcases p16266_3 (m.d 1 2) (by simp) with h16285 | h16285
                            · linarith only [h0, h16285, hlam]
                            · rcases p16266_3 (m.d 2 3) (by simp) with h16287 | h16287
                              · linarith only [h16287, h4, hlam]
                              · rcases p16266_3 (m.d 2 4) (by simp) with h16289 | h16289
                                · linarith only [h16289, hlam, p16266_0]
                                · rcases p16266_3 (m.d 2 5) (by simp) with h16291 | h16291
                                  · linarith only [h16291, h6, hlam]
                                  · rcases h4bigk with h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c | h16293c
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [hlam, p16293_0]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      rcases p16293_3 (m.d 0 4) (by simp) with h16295 | h16295
                                      · rcases p16293_3 (m.d 1 4) (by simp) with h16296 | h16296
                                        · linarith only [h16296, h2, hlam]
                                        · rcases p16293_3 (m.d 2 4) (by simp) with h16298 | h16298
                                          · linarith only [h16298, h5, hlam]
                                          · linarith only [h15885, h16298, hlam]
                                      · linarith only [h16295, h2, hlam]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h14160, h15906, h15908, h7, hc12, hc34, hlam, hphi, ht23, p16293_1]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h7, hlam, p16293_1]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      rcases p16293_3 (m.d 0 4) (by simp) with h16304 | h16304
                                      · rcases p16293_3 (m.d 1 4) (by simp) with h16305 | h16305
                                        · linarith only [h16305, h2, hlam]
                                        · linarith only [h15903, h16305, hlam]
                                      · linarith only [h16304, hlam, p16293_0]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h2, hlam, p16293_0]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [hlam, p16293_0]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h15885, hlam, p16293_1]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h15899, hlam, p16293_1]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p15910_1, p16293_1]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h5, hlam, p16293_0]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p16266_1, p16293_1]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [hlam, p16293_0]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h15904, hlam, p16293_1]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p16266_1, p16293_1]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h14160, h4, h7, hc12, hc34, hlam, hphi, ht23, p16293_1]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      rcases p16293_3 (m.d 0 4) (by simp) with h16320 | h16320
                                      · linarith only [h16320, h7, hlam]
                                      · linarith only [h16320, h2, hlam]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h15885, hc12, hc34, hlam, hphi, ht23, p16293_1]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [hlam, p16293_0]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      rcases p16293_3 (m.d 0 4) (by simp) with h16325 | h16325
                                      · linarith only [h16325, h7, hlam]
                                      · linarith only [h14159, h16325, hlam]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h14159, hlam, p16293_0]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h15903, hlam, p16293_0]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h15908, hlam, p16293_0]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [h15909, hlam, p16293_0]
                                    · have p16293_0 := h16293c.1
                                      have p16293_1 := h16293c.2.1
                                      have p16293_2 := h16293c.2.2.1
                                      have p16293_3 := h16293c.2.2.2
                                      linarith only [hlam, p16293_0]
                          · linarith only [h16284, hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          rcases p16266_3 (m.d 0 2) (by simp) with h16334 | h16334
                          · rcases p16266_3 (m.d 1 2) (by simp) with h16335 | h16335
                            · linarith only [h0, h16335, hlam]
                            · rcases p16266_3 (m.d 2 3) (by simp) with h16337 | h16337
                              · linarith only [h16337, h4, hlam]
                              · rcases p16266_3 (m.d 2 4) (by simp) with h16339 | h16339
                                · linarith only [h16339, h5, hlam]
                                · linarith only [h15908, h16339, hlam]
                          · linarith only [h16334, hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h0, hlam, p16266_1]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h14160, hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h15885, hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h15893, hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h4, hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p16266_1]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h15904, hlam, p16266_1]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h15906, hlam, p16266_1]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h5, hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          rcases p16266_3 (m.d 0 2) (by simp) with h16354 | h16354
                          · rcases p16266_3 (m.d 1 2) (by simp) with h16355 | h16355
                            · linarith only [h16355, hlam, p16266_0]
                            · rcases p16266_3 (m.d 2 3) (by simp) with h16357 | h16357
                              · linarith only [h15904, h16357, hlam]
                              · linarith only [h14160, h16357, hlam]
                          · linarith only [h0, h16354, hlam]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h0, h14160, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16266_1]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h0, h14160, h15906, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16266_1]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h6, hlam, p16266_0]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          rcases p16266_3 (m.d 0 2) (by simp) with h16365 | h16365
                          · rcases p16266_3 (m.d 1 2) (by simp) with h16366 | h16366
                            · linarith only [h16366, hlam, p16266_0]
                            · rcases p16266_3 (m.d 2 3) (by simp) with h16368 | h16368
                              · linarith only [h15906, h16368, hlam]
                              · linarith only [h14160, h16368, hlam]
                          · linarith only [h0, h16365, hlam]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p16266_1]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [h15908, hlam, p16266_1]
                        · have p16266_0 := h16266c.1
                          have p16266_1 := h16266c.2.1
                          have p16266_2 := h16266c.2.2.1
                          have p16266_3 := h16266c.2.2.2
                          linarith only [hlam, p16266_0]
            · linarith only [h15928, hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            rcases p15910_3 (m.d 0 1) (by simp) with h16376 | h16376
            · rcases p15910_3 (m.d 1 2) (by simp) with h16377 | h16377
              · linarith only [h0, h16377, hlam]
              · rcases p15910_3 (m.d 1 3) (by simp) with h16379 | h16379
                · linarith only [h1, h16379, hlam]
                · rcases p15910_3 (m.d 1 4) (by simp) with h16381 | h16381
                  · linarith only [h16381, h2, hlam]
                  · linarith only [h15903, h16381, hlam]
            · linarith only [h16376, hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [h0, hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [h14160, hlam, p15910_1]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [h15885, hlam, p15910_1]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [h15893, hlam, p15910_1]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [h1, hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [h1, h13284, h15909, hc12, hc34, hlam, hphi, ht23, p15910_1]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [h15899, hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [h15901, hlam, p15910_1]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [h2, hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            rcases p15910_3 (m.d 0 1) (by simp) with h16396 | h16396
            · rcases p15910_3 (m.d 1 2) (by simp) with h16397 | h16397
              · linarith only [h15885, h16397, hlam]
              · rcases p15910_3 (m.d 1 3) (by simp) with h16399 | h16399
                · linarith only [h15899, h16399, hlam]
                · linarith only [h14160, h16399, hlam]
            · linarith only [h0, h16396, hlam]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            rcases p15910_3 (m.d 0 1) (by simp) with h16403 | h16403
            · rcases p15910_3 (m.d 1 2) (by simp) with h16404 | h16404
              · linarith only [h15885, h16404, hlam]
              · rcases p15910_3 (m.d 1 3) (by simp) with h16406 | h16406
                · linarith only [h15899, h16406, hlam]
                · rcases p15910_3 (m.d 1 4) (by simp) with h16408 | h16408
                  · rcases p15910_3 (m.d 1 5) (by simp) with h16409 | h16409
                    · linarith only [h15903, h16409, hlam]
                    · linarith only [h15901, h16409, hlam]
                  · linarith only [h15899, h16408, hlam]
            · linarith only [h1, h16403, hlam]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            rcases p15910_3 (m.d 0 1) (by simp) with h16415 | h16415
            · rcases p15910_3 (m.d 1 2) (by simp) with h16416 | h16416
              · linarith only [h15885, h16416, hlam]
              · rcases p15910_3 (m.d 1 3) (by simp) with h16418 | h16418
                · linarith only [h15899, h16418, hlam]
                · rcases p15910_3 (m.d 1 4) (by simp) with h16420 | h16420
                  · rcases p15910_3 (m.d 1 5) (by simp) with h16421 | h16421
                    · linarith only [h15903, h16421, hlam]
                    · rcases h1emax with h16423 | h16423 | h16423 | h16423 | h16423
                      · linarith only [h0, h15885, h15901, h16423, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15910_1]
                      · rcases h2bigk with h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c | h16425c
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [hlam, p16425_0]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h14160, h15885, h15901, h5, hlam, p15910_1, p16425_2]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          rcases p16425_3 (m.d 0 2) (by simp) with h16428 | h16428
                          · rcases p16425_3 (m.d 1 2) (by simp) with h16429 | h16429
                            · linarith only [h0, h16429, hlam]
                            · rcases p16425_3 (m.d 2 3) (by simp) with h16431 | h16431
                              · linarith only [h16431, hlam, p16425_0]
                              · rcases p16425_3 (m.d 2 4) (by simp) with h16433 | h16433
                                · linarith only [h16433, h5, hlam]
                                · linarith only [h15904, h16433, hlam]
                          · linarith only [h16428, hlam, p16425_0]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h0, h14160, h15885, h15901, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15910_1, p16425_1]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          rcases p16425_3 (m.d 0 2) (by simp) with h16438 | h16438
                          · rcases p16425_3 (m.d 1 2) (by simp) with h16439 | h16439
                            · linarith only [h0, h16439, hlam]
                            · rcases p16425_3 (m.d 2 3) (by simp) with h16441 | h16441
                              · linarith only [h16441, h4, hlam]
                              · rcases p16425_3 (m.d 2 4) (by simp) with h16443 | h16443
                                · linarith only [h16443, h5, hlam]
                                · linarith only [h15908, h16443, hlam]
                          · linarith only [h16438, hlam, p16425_0]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h0, hlam, p16425_1]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [hlam, p16425_0]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h14160, hlam, p16425_0]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h15885, hlam, p16425_0]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h15893, hlam, p16425_0]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h4, hlam, p16425_0]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p16425_1]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [hlam, p16425_0]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h15904, hlam, p16425_1]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h15906, hlam, p16425_1]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h5, hlam, p16425_0]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          rcases p16425_3 (m.d 0 2) (by simp) with h16458 | h16458
                          · rcases p16425_3 (m.d 1 2) (by simp) with h16459 | h16459
                            · linarith only [h16459, hlam, p16425_0]
                            · rcases p16425_3 (m.d 2 3) (by simp) with h16461 | h16461
                              · linarith only [h15904, h16461, hlam]
                              · linarith only [h14160, h16461, hlam]
                          · linarith only [h0, h16458, hlam]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h0, h14160, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16425_1]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [hlam, p16425_0]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h0, h14160, h15906, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16425_1]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h6, hlam, p16425_0]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          rcases p16425_3 (m.d 0 2) (by simp) with h16469 | h16469
                          · rcases p16425_3 (m.d 1 2) (by simp) with h16470 | h16470
                            · linarith only [h16470, hlam, p16425_0]
                            · rcases p16425_3 (m.d 2 3) (by simp) with h16472 | h16472
                              · linarith only [h15906, h16472, hlam]
                              · linarith only [h14160, h16472, hlam]
                          · linarith only [h0, h16469, hlam]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p16425_1]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [h15908, hlam, p16425_1]
                        · have p16425_0 := h16425c.1
                          have p16425_1 := h16425c.2.1
                          have p16425_2 := h16425c.2.2.1
                          have p16425_3 := h16425c.2.2.2
                          linarith only [hlam, p16425_0]
                      · rcases h2bigk with h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [hlam, p16479_0]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h14160, h15885, h15901, h5, hlam, p15910_1, p16479_2]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          rcases p16479_3 (m.d 0 2) (by simp) with h16482 | h16482
                          · rcases p16479_3 (m.d 1 2) (by simp) with h16483 | h16483
                            · linarith only [h0, h16483, hlam]
                            · rcases p16479_3 (m.d 2 3) (by simp) with h16485 | h16485
                              · linarith only [h16485, hlam, p16479_0]
                              · rcases p16479_3 (m.d 2 4) (by simp) with h16487 | h16487
                                · linarith only [h16487, h5, hlam]
                                · linarith only [h15904, h16487, hlam]
                          · linarith only [h16482, hlam, p16479_0]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h14160, h15885, h15901, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15910_1, p16479_1]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          rcases p16479_3 (m.d 0 2) (by simp) with h16492 | h16492
                          · rcases p16479_3 (m.d 1 2) (by simp) with h16493 | h16493
                            · linarith only [h0, h16493, hlam]
                            · rcases p16479_3 (m.d 2 3) (by simp) with h16495 | h16495
                              · linarith only [h16495, h4, hlam]
                              · rcases p16479_3 (m.d 2 4) (by simp) with h16497 | h16497
                                · linarith only [h16497, h5, hlam]
                                · linarith only [h15908, h16497, hlam]
                          · linarith only [h16492, hlam, p16479_0]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h0, hlam, p16479_1]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [hlam, p16479_0]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h14160, hlam, p16479_0]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h15885, hlam, p16479_0]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h15893, hlam, p16479_0]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h4, hlam, p16479_0]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h13284, h15909, h4, hc12, hc34, hlam, hphi, ht23, p16479_1]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [hlam, p16479_0]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h15904, hlam, p16479_1]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h15906, hlam, p16479_1]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h5, hlam, p16479_0]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          rcases p16479_3 (m.d 0 2) (by simp) with h16512 | h16512
                          · rcases p16479_3 (m.d 1 2) (by simp) with h16513 | h16513
                            · linarith only [h16513, hlam, p16479_0]
                            · rcases p16479_3 (m.d 2 3) (by simp) with h16515 | h16515
                              · linarith only [h15904, h16515, hlam]
                              · linarith only [h14160, h16515, hlam]
                          · linarith only [h0, h16512, hlam]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h0, h14160, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16479_1]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [hlam, p16479_0]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h0, h14160, h15906, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16479_1]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h6, hlam, p16479_0]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          rcases p16479_3 (m.d 0 2) (by simp) with h16523 | h16523
                          · rcases p16479_3 (m.d 1 2) (by simp) with h16524 | h16524
                            · linarith only [h16524, hlam, p16479_0]
                            · rcases p16479_3 (m.d 2 3) (by simp) with h16526 | h16526
                              · linarith only [h15906, h16526, hlam]
                              · linarith only [h14160, h16526, hlam]
                          · linarith only [h0, h16523, hlam]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p16479_1]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [h15908, hlam, p16479_1]
                        · have p16479_0 := h16479c.1
                          have p16479_1 := h16479c.2.1
                          have p16479_2 := h16479c.2.2.1
                          have p16479_3 := h16479c.2.2.2
                          linarith only [hlam, p16479_0]
                      · linarith only [h14160, h15901, h16423, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p15910_1]
                      · rcases h2bigk with h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c | h16534c
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [hlam, p16534_0]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h14160, h15885, h15901, h5, hlam, p15910_1, p16534_2]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          rcases p16534_3 (m.d 0 2) (by simp) with h16537 | h16537
                          · rcases p16534_3 (m.d 1 2) (by simp) with h16538 | h16538
                            · linarith only [h0, h16538, hlam]
                            · rcases p16534_3 (m.d 2 3) (by simp) with h16540 | h16540
                              · linarith only [h16540, hlam, p16534_0]
                              · rcases p16534_3 (m.d 2 4) (by simp) with h16542 | h16542
                                · linarith only [h16542, h5, hlam]
                                · linarith only [h15904, h16542, hlam]
                          · linarith only [h16537, hlam, p16534_0]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h14160, h15885, h15901, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15910_1, p16534_1]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          rcases p16534_3 (m.d 0 2) (by simp) with h16547 | h16547
                          · rcases p16534_3 (m.d 1 2) (by simp) with h16548 | h16548
                            · linarith only [h0, h16548, hlam]
                            · rcases p16534_3 (m.d 2 3) (by simp) with h16550 | h16550
                              · linarith only [h16550, h4, hlam]
                              · rcases p16534_3 (m.d 2 4) (by simp) with h16552 | h16552
                                · linarith only [h16552, h5, hlam]
                                · linarith only [h15908, h16552, hlam]
                          · linarith only [h16547, hlam, p16534_0]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h0, hlam, p16534_1]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [hlam, p16534_0]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h14160, hlam, p16534_0]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h15885, hlam, p16534_0]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h15893, hlam, p16534_0]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h4, hlam, p16534_0]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h13284, h15909, h4, hc12, hc34, hlam, hphi, ht23, p16534_1]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [hlam, p16534_0]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h15904, hlam, p16534_1]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h15906, hlam, p16534_1]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h5, hlam, p16534_0]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          rcases p16534_3 (m.d 0 2) (by simp) with h16567 | h16567
                          · rcases p16534_3 (m.d 1 2) (by simp) with h16568 | h16568
                            · linarith only [h16568, hlam, p16534_0]
                            · rcases p16534_3 (m.d 2 3) (by simp) with h16570 | h16570
                              · linarith only [h15904, h16570, hlam]
                              · linarith only [h14160, h16570, hlam]
                          · linarith only [h0, h16567, hlam]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h0, h14160, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16534_1]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [hlam, p16534_0]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h0, h14160, h15906, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16534_1]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h6, hlam, p16534_0]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          rcases p16534_3 (m.d 0 2) (by simp) with h16578 | h16578
                          · rcases p16534_3 (m.d 1 2) (by simp) with h16579 | h16579
                            · linarith only [h16579, hlam, p16534_0]
                            · rcases p16534_3 (m.d 2 3) (by simp) with h16581 | h16581
                              · linarith only [h15906, h16581, hlam]
                              · linarith only [h14160, h16581, hlam]
                          · linarith only [h0, h16578, hlam]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p16534_1]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [h15908, hlam, p16534_1]
                        · have p16534_0 := h16534c.1
                          have p16534_1 := h16534c.2.1
                          have p16534_2 := h16534c.2.2.1
                          have p16534_3 := h16534c.2.2.2
                          linarith only [hlam, p16534_0]
                  · linarith only [h15903, h16420, hlam]
            · linarith only [h16415, h3, hlam]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [h3, hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            rcases p15910_3 (m.d 0 1) (by simp) with h16591 | h16591
            · rcases p15910_3 (m.d 1 2) (by simp) with h16592 | h16592
              · linarith only [h15893, h16592, hlam]
              · rcases p15910_3 (m.d 1 3) (by simp) with h16594 | h16594
                · linarith only [h15901, h16594, hlam]
                · linarith only [h14160, h16594, hlam]
            · linarith only [h0, h16591, hlam]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            rcases p15910_3 (m.d 0 1) (by simp) with h16598 | h16598
            · rcases p15910_3 (m.d 1 2) (by simp) with h16599 | h16599
              · linarith only [h15893, h16599, hlam]
              · rcases p15910_3 (m.d 1 3) (by simp) with h16601 | h16601
                · linarith only [h15901, h16601, hlam]
                · rcases p15910_3 (m.d 1 4) (by simp) with h16603 | h16603
                  · rcases p15910_3 (m.d 1 5) (by simp) with h16604 | h16604
                    · rcases h1emax with h16605 | h16605 | h16605 | h16605 | h16605
                      · linarith only [h14160, h16605, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p15910_1]
                      · rcases h2bigk with h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c | h16607c
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [hlam, p16607_0]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h14160, h15893, h15908, h5, hlam, p15910_1, p16607_2]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          rcases p16607_3 (m.d 0 2) (by simp) with h16610 | h16610
                          · rcases p16607_3 (m.d 1 2) (by simp) with h16611 | h16611
                            · linarith only [h0, h16611, hlam]
                            · rcases p16607_3 (m.d 2 3) (by simp) with h16613 | h16613
                              · linarith only [h16613, hlam, p16607_0]
                              · rcases p16607_3 (m.d 2 4) (by simp) with h16615 | h16615
                                · linarith only [h16615, h5, hlam]
                                · linarith only [h15904, h16615, hlam]
                          · linarith only [h16610, hlam, p16607_0]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h0, h14160, h15893, h15908, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15910_1, p16607_1]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h0, h14160, h15893, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15910_1, p16607_1]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h0, hlam, p16607_1]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [hlam, p16607_0]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h14160, hlam, p16607_0]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h15885, hlam, p16607_0]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h15893, hlam, p16607_0]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h4, hlam, p16607_0]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h13284, h15909, h4, hc12, hc34, hlam, hphi, ht23, p16607_1]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [hlam, p16607_0]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h15904, hlam, p16607_1]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h15906, hlam, p16607_1]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h5, hlam, p16607_0]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          rcases p16607_3 (m.d 0 2) (by simp) with h16632 | h16632
                          · rcases p16607_3 (m.d 1 2) (by simp) with h16633 | h16633
                            · linarith only [h16633, hlam, p16607_0]
                            · rcases p16607_3 (m.d 2 3) (by simp) with h16635 | h16635
                              · linarith only [h15904, h16635, hlam]
                              · linarith only [h14160, h16635, hlam]
                          · linarith only [h0, h16632, hlam]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h14160, hc12, hc24, hlam, hphi, p16607_1]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [hlam, p16607_0]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h0, h14160, h15893, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15910_1, p16607_1]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h6, hlam, p16607_0]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          rcases p16607_3 (m.d 0 2) (by simp) with h16643 | h16643
                          · rcases p16607_3 (m.d 1 2) (by simp) with h16644 | h16644
                            · linarith only [h16644, hlam, p16607_0]
                            · rcases p16607_3 (m.d 2 3) (by simp) with h16646 | h16646
                              · linarith only [h15906, h16646, hlam]
                              · linarith only [h14160, h16646, hlam]
                          · linarith only [h0, h16643, hlam]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p16607_1]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [h15908, hlam, p16607_1]
                        · have p16607_0 := h16607c.1
                          have p16607_1 := h16607c.2.1
                          have p16607_2 := h16607c.2.2.1
                          have p16607_3 := h16607c.2.2.2
                          linarith only [hlam, p16607_0]
                      · rcases h2bigk with h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [hlam, p16653_0]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h14160, h15893, h15908, h5, hlam, p15910_1, p16653_2]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          rcases p16653_3 (m.d 0 2) (by simp) with h16656 | h16656
                          · rcases p16653_3 (m.d 1 2) (by simp) with h16657 | h16657
                            · linarith only [h0, h16657, hlam]
                            · rcases p16653_3 (m.d 2 3) (by simp) with h16659 | h16659
                              · linarith only [h16659, hlam, p16653_0]
                              · rcases p16653_3 (m.d 2 4) (by simp) with h16661 | h16661
                                · linarith only [h16661, h5, hlam]
                                · linarith only [h15904, h16661, hlam]
                          · linarith only [h16656, hlam, p16653_0]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h0, h14160, h15893, h15908, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15910_1, p16653_1]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h0, h14160, h15893, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15910_1, p16653_1]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h0, hlam, p16653_1]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [hlam, p16653_0]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h14160, hlam, p16653_0]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h15885, hlam, p16653_0]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h15893, hlam, p16653_0]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h4, hlam, p16653_0]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h13284, h15909, h4, hc12, hc34, hlam, hphi, ht23, p16653_1]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [hlam, p16653_0]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h15904, hlam, p16653_1]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h15906, hlam, p16653_1]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h5, hlam, p16653_0]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          rcases p16653_3 (m.d 0 2) (by simp) with h16678 | h16678
                          · rcases p16653_3 (m.d 1 2) (by simp) with h16679 | h16679
                            · linarith only [h16679, hlam, p16653_0]
                            · rcases p16653_3 (m.d 2 3) (by simp) with h16681 | h16681
                              · linarith only [h15904, h16681, hlam]
                              · linarith only [h14160, h16681, hlam]
                          · linarith only [h0, h16678, hlam]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h14160, hc12, hc24, hlam, hphi, p16653_1]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [hlam, p16653_0]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h0, h14160, h15893, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15910_1, p16653_1]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h6, hlam, p16653_0]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          rcases p16653_3 (m.d 0 2) (by simp) with h16689 | h16689
                          · rcases p16653_3 (m.d 1 2) (by simp) with h16690 | h16690
                            · linarith only [h16690, hlam, p16653_0]
                            · rcases p16653_3 (m.d 2 3) (by simp) with h16692 | h16692
                              · linarith only [h15906, h16692, hlam]
                              · linarith only [h14160, h16692, hlam]
                          · linarith only [h0, h16689, hlam]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p16653_1]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [h15908, hlam, p16653_1]
                        · have p16653_0 := h16653c.1
                          have p16653_1 := h16653c.2.1
                          have p16653_2 := h16653c.2.2.1
                          have p16653_3 := h16653c.2.2.2
                          linarith only [hlam, p16653_0]
                      · linarith only [h14160, h15903, h16605, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p15910_1]
                      · linarith only [h14160, h16605, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p15910_1]
                    · linarith only [h15901, h16604, hlam]
                  · linarith only [h15899, h16603, hlam]
            · linarith only [h1, h16598, hlam]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [h15903, hlam, p15910_0]
          · have p15910_0 := h15910c.1
            have p15910_1 := h15910c.2.1
            have p15910_2 := h15910c.2.2.1
            have p15910_3 := h15910c.2.2.2
            linarith only [hlam, p15910_0]
        · linarith only [h14160, h15909, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
      · linarith only [h15885, h15903, h15908, hlam]

end R2N4
