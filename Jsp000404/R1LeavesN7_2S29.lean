import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S28

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20419 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h20420 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20421 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20422 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 3 4 5 (by decide) (by decide) with h20907 | h20907
  · linarith only [h0, h20408, h20420, h20422, h20907, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
  · rcases h0bigk with h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c | h20909c
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [hlam, p20909_0]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h0, hlam, p20909_1]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h14396, hlam, p20909_0]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h16915, hlam, p20909_1]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h18815, hlam, p20909_1]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      rcases p20909_3 (m.d 0 1) (by simp) with h20915 | h20915
      · linarith only [h0, h20915, hlam]
      · rcases p20909_3 (m.d 0 2) (by simp) with h20917 | h20917
        · rcases p20909_3 (m.d 0 3) (by simp) with h20918 | h20918
          · linarith only [h20408, h20918, hlam]
          · linarith only [h14396, h20918, hlam]
        · linarith only [h0, h20917, hlam]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [hlam, p20909_0]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h0, h20411, h20413, h20420, h20422, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20909_1]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h0, h20413, h20420, h20422, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20909_1]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      rcases p20909_3 (m.d 0 1) (by simp) with h20925 | h20925
      · linarith only [h0, h20925, hlam]
      · rcases p20909_3 (m.d 0 2) (by simp) with h20927 | h20927
        · rcases p20909_3 (m.d 0 3) (by simp) with h20928 | h20928
          · linarith only [h20408, h20928, hlam]
          · linarith only [h20412, h20928, hlam]
        · linarith only [h20410, h20927, hlam]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      rcases p20909_3 (m.d 0 1) (by simp) with h20932 | h20932
      · linarith only [h14396, h20932, hlam]
      · rcases p20909_3 (m.d 0 2) (by simp) with h20934 | h20934
        · rcases p20909_3 (m.d 0 3) (by simp) with h20935 | h20935
          · rcases p20909_3 (m.d 0 4) (by simp) with h20936 | h20936
            · linarith only [h20411, h20936, hlam]
            · linarith only [h16915, h20936, hlam]
          · linarith only [h14396, h20935, hlam]
        · linarith only [h0, h20934, hlam]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h20408, hlam, p20909_1]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [hlam, p20909_0]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h20413, h20420, h20422, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p20909_1]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      rcases p20909_3 (m.d 0 1) (by simp) with h20944 | h20944
      · linarith only [h14396, h20944, hlam]
      · rcases p20909_3 (m.d 0 2) (by simp) with h20946 | h20946
        · rcases p20909_3 (m.d 0 3) (by simp) with h20947 | h20947
          · rcases p20909_3 (m.d 0 4) (by simp) with h20948 | h20948
            · linarith only [h20411, h20948, hlam]
            · linarith only [h20413, h20948, hlam]
          · linarith only [h20412, h20947, hlam]
        · linarith only [h20410, h20946, hlam]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      rcases p20909_3 (m.d 0 1) (by simp) with h20953 | h20953
      · linarith only [h16915, h20953, hlam]
      · rcases p20909_3 (m.d 0 2) (by simp) with h20955 | h20955
        · rcases p20909_3 (m.d 0 3) (by simp) with h20956 | h20956
          · rcases p20909_3 (m.d 0 4) (by simp) with h20957 | h20957
            · rcases p20909_3 (m.d 0 5) (by simp) with h20958 | h20958
              · linarith only [h20413, h20958, hlam]
              · linarith only [h18815, h20958, hlam]
            · linarith only [h16915, h20957, hlam]
          · linarith only [h14396, h20956, hlam]
        · linarith only [h0, h20955, hlam]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h20409, hlam, p20909_0]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h20411, hlam, p20909_0]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [hlam, p20909_0]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      rcases p20909_3 (m.d 0 1) (by simp) with h20967 | h20967
      · linarith only [h16915, h20967, hlam]
      · rcases p20909_3 (m.d 0 2) (by simp) with h20969 | h20969
        · rcases p20909_3 (m.d 0 3) (by simp) with h20970 | h20970
          · rcases p20909_3 (m.d 0 4) (by simp) with h20971 | h20971
            · rcases p20909_3 (m.d 0 5) (by simp) with h20972 | h20972
              · linarith only [h20413, h20972, hlam]
              · rcases h2bigk with h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c | h20974c
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [hlam, p20974_0]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h0, hlam, p20974_1]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  rcases p20974_3 (m.d 0 2) (by simp) with h20977 | h20977
                  · rcases p20974_3 (m.d 1 2) (by simp) with h20978 | h20978
                    · rcases p20974_3 (m.d 2 3) (by simp) with h20979 | h20979
                      · linarith only [h20979, hlam, p20974_0]
                      · rcases p20974_3 (m.d 2 4) (by simp) with h20981 | h20981
                        · linarith only [h20409, h20981, hlam]
                        · rcases p20974_3 (m.d 2 5) (by simp) with h20983 | h20983
                          · linarith only [h20410, h20983, hlam]
                          · rcases h3bigk with h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c | h20985c
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h14396, hlam, p20985_1]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h20408, hlam, p20974_2, p20985_1]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              rcases p20985_3 (m.d 0 3) (by simp) with h20989 | h20989
                              · rcases p20985_3 (m.d 1 3) (by simp) with h20990 | h20990
                                · rcases p20985_3 (m.d 2 3) (by simp) with h20991 | h20991
                                  · linarith only [h20408, h20991, hlam]
                                  · linarith only [h20420, h20991, hlam]
                                · linarith only [h20417, h20990, hlam]
                              · linarith only [h20989, hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              rcases p20985_3 (m.d 0 3) (by simp) with h20996 | h20996
                              · rcases p20985_3 (m.d 1 3) (by simp) with h20997 | h20997
                                · rcases p20985_3 (m.d 2 3) (by simp) with h20998 | h20998
                                  · linarith only [h20408, h20998, hlam]
                                  · linarith only [h20421, h20998, hlam]
                                · linarith only [h20418, h20997, hlam]
                              · linarith only [h20996, hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p20985_1]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h20414, h20421, h20907, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20985_1]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              rcases p20985_3 (m.d 0 3) (by simp) with h21006 | h21006
                              · linarith only [h14396, h21006, hlam]
                              · linarith only [h20411, h21006, hlam]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              rcases p20985_3 (m.d 0 3) (by simp) with h21009 | h21009
                              · linarith only [h14396, h21009, hlam]
                              · linarith only [h20412, h21009, hlam]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h20408, hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h20414, hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p20974_1, p20985_1]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h0, h20907, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20974_1, p20985_1]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h20411, hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h20417, hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h20420, hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h20907, hlam, p20985_1]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h20412, hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h20418, hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h20421, hlam, p20985_0]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [h20412, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p20985_1]
                            · have p20985_0 := h20985c.1
                              have p20985_1 := h20985c.2.1
                              have p20985_2 := h20985c.2.2.1
                              have p20985_3 := h20985c.2.2.2
                              linarith only [hlam, p20985_0]
                    · linarith only [h20414, h20978, hlam]
                  · linarith only [h20977, hlam, p20974_0]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h20408, h20411, h20413, h20422, hlam, p20909_1, p20974_2]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  rcases p20974_3 (m.d 0 2) (by simp) with h21030 | h21030
                  · rcases p20974_3 (m.d 1 2) (by simp) with h21031 | h21031
                    · rcases p20974_3 (m.d 2 3) (by simp) with h21032 | h21032
                      · linarith only [h20408, h21032, hlam]
                      · linarith only [h20421, h21032, hlam]
                    · linarith only [h20416, h21031, hlam]
                  · linarith only [h21030, hlam, p20974_0]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h20408, h20411, h20413, h20420, h20422, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20909_1, p20974_1]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [hlam, p20974_0]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  rcases p20974_3 (m.d 0 2) (by simp) with h21039 | h21039
                  · linarith only [h0, h21039, hlam]
                  · linarith only [h20408, h21039, hlam]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h0, h20408, h20411, h20413, h20422, hlam, p20909_1, p20974_2]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  rcases p20974_3 (m.d 0 2) (by simp) with h21043 | h21043
                  · linarith only [h0, h21043, hlam]
                  · linarith only [h20410, h21043, hlam]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h20408, hlam, p20974_0]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h20414, hlam, p20974_0]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [hlam, p20974_0]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  rcases p20974_3 (m.d 0 2) (by simp) with h21049 | h21049
                  · rcases p20974_3 (m.d 1 2) (by simp) with h21050 | h21050
                    · rcases p20974_3 (m.d 2 3) (by simp) with h21051 | h21051
                      · rcases p20974_3 (m.d 2 4) (by simp) with h21052 | h21052
                        · linarith only [h20420, h21052, hlam]
                        · rcases p20974_3 (m.d 2 5) (by simp) with h21054 | h21054
                          · linarith only [h20421, h21054, hlam]
                          · linarith only [h20422, h21054, hlam]
                      · linarith only [h20420, h21051, hlam]
                    · linarith only [h20415, h21050, hlam]
                  · linarith only [h20409, h21049, hlam]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  rcases p20974_3 (m.d 0 2) (by simp) with h21060 | h21060
                  · rcases p20974_3 (m.d 1 2) (by simp) with h21061 | h21061
                    · rcases p20974_3 (m.d 2 3) (by simp) with h21062 | h21062
                      · rcases p20974_3 (m.d 2 4) (by simp) with h21063 | h21063
                        · linarith only [h20420, h21063, hlam]
                        · rcases p20974_3 (m.d 2 5) (by simp) with h21065 | h21065
                          · linarith only [h20421, h21065, hlam]
                          · rcases h3bigk with h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h14396, hlam, p21067_1]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20408, hc02, hc25, hlam, hphi, ht0b, ht5b, p20974_1, p21067_1]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              rcases p21067_3 (m.d 0 3) (by simp) with h21071 | h21071
                              · rcases p21067_3 (m.d 1 3) (by simp) with h21072 | h21072
                                · rcases p21067_3 (m.d 2 3) (by simp) with h21073 | h21073
                                  · linarith only [h20408, h21073, hlam]
                                  · linarith only [h20420, h21073, hlam]
                                · linarith only [h20417, h21072, hlam]
                              · linarith only [h21071, hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              rcases p21067_3 (m.d 0 3) (by simp) with h21078 | h21078
                              · rcases p21067_3 (m.d 1 3) (by simp) with h21079 | h21079
                                · rcases p21067_3 (m.d 2 3) (by simp) with h21080 | h21080
                                  · linarith only [h20408, h21080, hlam]
                                  · linarith only [h20421, h21080, hlam]
                                · linarith only [h20418, h21079, hlam]
                              · linarith only [h21078, hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20411, h20413, h20414, h20420, h20422, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20909_1, p21067_1]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20414, h20420, h20422, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20974_1, p21067_1]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              rcases p21067_3 (m.d 0 3) (by simp) with h21088 | h21088
                              · linarith only [h14396, h21088, hlam]
                              · linarith only [h20411, h21088, hlam]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              rcases p21067_3 (m.d 0 3) (by simp) with h21091 | h21091
                              · linarith only [h14396, h21091, hlam]
                              · linarith only [h20412, h21091, hlam]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20408, hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20414, hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20408, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p21067_1]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h0, h20408, h20907, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21067_1]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20411, hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20417, hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20420, hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20907, hlam, p21067_1]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20412, hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20418, hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20421, hlam, p21067_0]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [h20412, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p21067_1]
                            · have p21067_0 := h21067c.1
                              have p21067_1 := h21067c.2.1
                              have p21067_2 := h21067c.2.2.1
                              have p21067_3 := h21067c.2.2.2
                              linarith only [hlam, p21067_0]
                      · linarith only [h20421, h21062, hlam]
                    · linarith only [h20416, h21061, hlam]
                  · linarith only [h20410, h21060, hlam]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h20409, hlam, p20974_0]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h20415, hlam, p20974_0]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h20420, hlam, p20974_1]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [hlam, p20974_0]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h20422, hlam, p20974_1]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h20410, hlam, p20974_0]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h20416, hlam, p20974_0]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h20421, hlam, p20974_1]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [h20410, h20420, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p20909_1, p20974_1]
                · have p20974_0 := h20974c.1
                  have p20974_1 := h20974c.2.1
                  have p20974_2 := h20974c.2.2.1
                  have p20974_3 := h20974c.2.2.2
                  linarith only [hlam, p20974_0]
            · linarith only [h20413, h20971, hlam]
          · linarith only [h20412, h20970, hlam]
        · linarith only [h20410, h20969, hlam]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      rcases p20909_3 (m.d 0 1) (by simp) with h21125 | h21125
      · linarith only [h18815, h21125, hlam]
      · rcases p20909_3 (m.d 0 2) (by simp) with h21127 | h21127
        · rcases p20909_3 (m.d 0 3) (by simp) with h21128 | h21128
          · rcases p20909_3 (m.d 0 4) (by simp) with h21129 | h21129
            · rcases p20909_3 (m.d 0 5) (by simp) with h21130 | h21130
              · rcases h2bigk with h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c | h21131c
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [h0, hlam, p21131_1]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  rcases p21131_3 (m.d 0 2) (by simp) with h21134 | h21134
                  · rcases p21131_3 (m.d 1 2) (by simp) with h21135 | h21135
                    · rcases p21131_3 (m.d 2 3) (by simp) with h21136 | h21136
                      · linarith only [h21136, hlam, p21131_0]
                      · rcases p21131_3 (m.d 2 4) (by simp) with h21138 | h21138
                        · linarith only [h20409, h21138, hlam]
                        · rcases p21131_3 (m.d 2 5) (by simp) with h21140 | h21140
                          · linarith only [h20410, h21140, hlam]
                          · rcases h3bigk with h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c | h21142c
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h14396, hlam, p21142_1]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h14396, h20414, h20421, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p21142_1]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              rcases p21142_3 (m.d 0 3) (by simp) with h21146 | h21146
                              · rcases p21142_3 (m.d 1 3) (by simp) with h21147 | h21147
                                · rcases p21142_3 (m.d 2 3) (by simp) with h21148 | h21148
                                  · linarith only [h20408, h21148, hlam]
                                  · linarith only [h20420, h21148, hlam]
                                · linarith only [h20417, h21147, hlam]
                              · linarith only [h21146, hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              rcases p21142_3 (m.d 0 3) (by simp) with h21153 | h21153
                              · rcases p21142_3 (m.d 1 3) (by simp) with h21154 | h21154
                                · rcases p21142_3 (m.d 2 3) (by simp) with h21155 | h21155
                                  · linarith only [h20408, h21155, hlam]
                                  · linarith only [h20421, h21155, hlam]
                                · linarith only [h20418, h21154, hlam]
                              · linarith only [h21153, hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p21142_1]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h20414, h20421, h20907, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21142_1]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              rcases p21142_3 (m.d 0 3) (by simp) with h21163 | h21163
                              · linarith only [h14396, h21163, hlam]
                              · linarith only [h20411, h21163, hlam]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              rcases p21142_3 (m.d 0 3) (by simp) with h21166 | h21166
                              · linarith only [h14396, h21166, hlam]
                              · linarith only [h20412, h21166, hlam]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h20408, hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h20414, hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21131_1, p21142_1]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h0, h20907, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21131_1, p21142_1]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h20411, hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h20417, hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h20420, hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h20907, hlam, p21142_1]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h20412, hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h20418, hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h20421, hlam, p21142_0]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [h20412, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p21142_1]
                            · have p21142_0 := h21142c.1
                              have p21142_1 := h21142c.2.1
                              have p21142_2 := h21142c.2.2.1
                              have p21142_3 := h21142c.2.2.2
                              linarith only [hlam, p21142_0]
                    · linarith only [h20414, h21135, hlam]
                  · linarith only [h21134, hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  rcases p21131_3 (m.d 0 2) (by simp) with h21186 | h21186
                  · rcases p21131_3 (m.d 1 2) (by simp) with h21187 | h21187
                    · rcases p21131_3 (m.d 2 3) (by simp) with h21188 | h21188
                      · linarith only [h20408, h21188, hlam]
                      · linarith only [h20420, h21188, hlam]
                    · linarith only [h20415, h21187, hlam]
                  · linarith only [h21186, hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  rcases p21131_3 (m.d 0 2) (by simp) with h21193 | h21193
                  · rcases p21131_3 (m.d 1 2) (by simp) with h21194 | h21194
                    · rcases p21131_3 (m.d 2 3) (by simp) with h21195 | h21195
                      · linarith only [h20408, h21195, hlam]
                      · linarith only [h20421, h21195, hlam]
                    · linarith only [h20416, h21194, hlam]
                  · linarith only [h21193, hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [h20408, h20421, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p21131_1]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  rcases p21131_3 (m.d 0 2) (by simp) with h21202 | h21202
                  · linarith only [h0, h21202, hlam]
                  · linarith only [h20408, h21202, hlam]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  rcases p21131_3 (m.d 0 2) (by simp) with h21205 | h21205
                  · linarith only [h0, h21205, hlam]
                  · linarith only [h20409, h21205, hlam]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  rcases p21131_3 (m.d 0 2) (by simp) with h21208 | h21208
                  · linarith only [h0, h21208, hlam]
                  · linarith only [h20410, h21208, hlam]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [h20408, hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [h20414, hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  rcases p21131_3 (m.d 0 2) (by simp) with h21214 | h21214
                  · rcases p21131_3 (m.d 1 2) (by simp) with h21215 | h21215
                    · rcases p21131_3 (m.d 2 3) (by simp) with h21216 | h21216
                      · rcases p21131_3 (m.d 2 4) (by simp) with h21217 | h21217
                        · linarith only [h20420, h21217, hlam]
                        · rcases p21131_3 (m.d 2 5) (by simp) with h21219 | h21219
                          · linarith only [h20421, h21219, hlam]
                          · linarith only [h20422, h21219, hlam]
                      · linarith only [h20420, h21216, hlam]
                    · linarith only [h20415, h21215, hlam]
                  · linarith only [h20409, h21214, hlam]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  rcases p21131_3 (m.d 0 2) (by simp) with h21225 | h21225
                  · rcases p21131_3 (m.d 1 2) (by simp) with h21226 | h21226
                    · rcases p21131_3 (m.d 2 3) (by simp) with h21227 | h21227
                      · rcases p21131_3 (m.d 2 4) (by simp) with h21228 | h21228
                        · linarith only [h20420, h21228, hlam]
                        · rcases p21131_3 (m.d 2 5) (by simp) with h21230 | h21230
                          · linarith only [h20421, h21230, hlam]
                          · rcases h3bigk with h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c | h21232c
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h14396, hlam, p21232_1]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h14396, h20414, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p21131_1, p21232_1]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              rcases p21232_3 (m.d 0 3) (by simp) with h21236 | h21236
                              · rcases p21232_3 (m.d 1 3) (by simp) with h21237 | h21237
                                · rcases p21232_3 (m.d 2 3) (by simp) with h21238 | h21238
                                  · linarith only [h20408, h21238, hlam]
                                  · linarith only [h20420, h21238, hlam]
                                · linarith only [h20417, h21237, hlam]
                              · linarith only [h21236, hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              rcases p21232_3 (m.d 0 3) (by simp) with h21243 | h21243
                              · rcases p21232_3 (m.d 1 3) (by simp) with h21244 | h21244
                                · rcases p21232_3 (m.d 2 3) (by simp) with h21245 | h21245
                                  · linarith only [h20408, h21245, hlam]
                                  · linarith only [h20421, h21245, hlam]
                                · linarith only [h20418, h21244, hlam]
                              · linarith only [h21243, hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p21232_1]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h20414, h20421, h20907, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21131_1, p21232_1]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              rcases p21232_3 (m.d 0 3) (by simp) with h21253 | h21253
                              · linarith only [h14396, h21253, hlam]
                              · linarith only [h20411, h21253, hlam]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              rcases p21232_3 (m.d 0 3) (by simp) with h21256 | h21256
                              · linarith only [h14396, h21256, hlam]
                              · linarith only [h20412, h21256, hlam]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h20408, hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h20414, hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h0, h20408, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21232_1]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h0, h20408, h20907, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21232_1]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h20411, hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h20417, hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h20420, hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h20907, hlam, p21232_1]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h20412, hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h20418, hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h20421, hlam, p21232_0]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [h0, h20410, h20421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21232_1]
                            · have p21232_0 := h21232c.1
                              have p21232_1 := h21232c.2.1
                              have p21232_2 := h21232c.2.2.1
                              have p21232_3 := h21232c.2.2.2
                              linarith only [hlam, p21232_0]
                      · linarith only [h20421, h21227, hlam]
                    · linarith only [h20416, h21226, hlam]
                  · linarith only [h20410, h21225, hlam]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [h20409, hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [h20415, hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [h20420, hlam, p21131_1]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [h20422, hlam, p21131_1]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [h20410, hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [h20416, hlam, p21131_0]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [h20421, hlam, p21131_1]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  rcases p21131_3 (m.d 0 2) (by simp) with h21285 | h21285
                  · rcases p21131_3 (m.d 1 2) (by simp) with h21286 | h21286
                    · rcases p21131_3 (m.d 2 3) (by simp) with h21287 | h21287
                      · rcases p21131_3 (m.d 2 4) (by simp) with h21288 | h21288
                        · linarith only [h20422, h21288, hlam]
                        · rcases p21131_3 (m.d 2 5) (by simp) with h21290 | h21290
                          · rcases h3bigk with h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c | h21291c
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h14396, hlam, p21291_1]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h20421, hc03, hc35, hlam, hphi, ht0b, ht5b, p21291_1]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              rcases p21291_3 (m.d 0 3) (by simp) with h21295 | h21295
                              · rcases p21291_3 (m.d 1 3) (by simp) with h21296 | h21296
                                · rcases p21291_3 (m.d 2 3) (by simp) with h21297 | h21297
                                  · linarith only [h20408, h21297, hlam]
                                  · linarith only [h20420, h21297, hlam]
                                · linarith only [h20417, h21296, hlam]
                              · linarith only [h21295, hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              rcases p21291_3 (m.d 0 3) (by simp) with h21302 | h21302
                              · rcases p21291_3 (m.d 1 3) (by simp) with h21303 | h21303
                                · rcases p21291_3 (m.d 2 3) (by simp) with h21304 | h21304
                                  · linarith only [h20408, h21304, hlam]
                                  · linarith only [h20421, h21304, hlam]
                                · linarith only [h20418, h21303, hlam]
                              · linarith only [h21302, hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p21291_1]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h20414, h20420, h20421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21131_1, p21291_1]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              rcases p21291_3 (m.d 0 3) (by simp) with h21312 | h21312
                              · linarith only [h14396, h21312, hlam]
                              · linarith only [h20411, h21312, hlam]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              rcases p21291_3 (m.d 0 3) (by simp) with h21315 | h21315
                              · linarith only [h14396, h21315, hlam]
                              · linarith only [h20412, h21315, hlam]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h20408, hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h20414, hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h0, h20408, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21291_1]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h0, h20408, h20907, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21291_1]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h20411, hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h20417, hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h20420, hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h20907, hlam, p21291_1]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h20412, hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h20418, hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h20421, hlam, p21291_0]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [h20412, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p21291_1]
                            · have p21291_0 := h21291c.1
                              have p21291_1 := h21291c.2.1
                              have p21291_2 := h21291c.2.2.1
                              have p21291_3 := h21291c.2.2.2
                              linarith only [hlam, p21291_0]
                          · linarith only [h20422, h21290, hlam]
                      · linarith only [h20420, h21287, hlam]
                    · linarith only [h20415, h21286, hlam]
                  · linarith only [h20409, h21285, hlam]
                · have p21131_0 := h21131c.1
                  have p21131_1 := h21131c.2.1
                  have p21131_2 := h21131c.2.2.1
                  have p21131_3 := h21131c.2.2.2
                  linarith only [hlam, p21131_0]
              · linarith only [h18815, h21130, hlam]
            · linarith only [h16915, h21129, hlam]
          · linarith only [h14396, h21128, hlam]
        · linarith only [h0, h21127, hlam]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h20410, hlam, p20909_1]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h20412, hlam, p20909_0]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [h20413, hlam, p20909_1]
    · have p20909_0 := h20909c.1
      have p20909_1 := h20909c.2.1
      have p20909_2 := h20909c.2.2.1
      have p20909_3 := h20909c.2.2.2
      linarith only [hlam, p20909_0]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20419 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h20420 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20421 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 2 4 5 (by decide) (by decide) with h20422 | h20422
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418 h20419 h20420 h20421 h20422
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418 h20419 h20420 h20421 h20422

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20419 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h20420 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20421 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 2 4 5 (by decide) (by decide) with h21346 | h21346
  · linarith only [h20420, h20421, h21346, hlam]
  · rcases m.htr 3 4 5 (by decide) (by decide) with h21348 | h21348
    · linarith only [h14396, h20412, h20414, h20420, h20421, h21346, h21348, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
    · rcases h0bigk with h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c | h21350c
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [hlam, p21350_0]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h0, hlam, p21350_1]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h14396, hlam, p21350_0]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h16915, hlam, p21350_1]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h18815, hlam, p21350_1]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        rcases p21350_3 (m.d 0 1) (by simp) with h21356 | h21356
        · linarith only [h0, h21356, hlam]
        · rcases p21350_3 (m.d 0 2) (by simp) with h21358 | h21358
          · rcases p21350_3 (m.d 0 3) (by simp) with h21359 | h21359
            · linarith only [h20408, h21359, hlam]
            · linarith only [h14396, h21359, hlam]
          · linarith only [h0, h21358, hlam]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [hlam, p21350_0]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h0, h20411, h20413, h20421, h21348, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21350_1]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h0, h20413, h20420, h20421, h21348, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21350_1]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h0, h20412, h20420, h20421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21350_1]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        rcases p21350_3 (m.d 0 1) (by simp) with h21367 | h21367
        · linarith only [h14396, h21367, hlam]
        · rcases p21350_3 (m.d 0 2) (by simp) with h21369 | h21369
          · rcases p21350_3 (m.d 0 3) (by simp) with h21370 | h21370
            · rcases p21350_3 (m.d 0 4) (by simp) with h21371 | h21371
              · linarith only [h20411, h21371, hlam]
              · linarith only [h16915, h21371, hlam]
            · linarith only [h14396, h21370, hlam]
          · linarith only [h0, h21369, hlam]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h20408, hlam, p21350_1]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [hlam, p21350_0]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h20413, h20420, h20421, h21348, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p21350_1]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h14396, h20413, h20414, h20420, h20421, h21348, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21350_1]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        rcases p21350_3 (m.d 0 1) (by simp) with h21380 | h21380
        · linarith only [h16915, h21380, hlam]
        · rcases p21350_3 (m.d 0 2) (by simp) with h21382 | h21382
          · rcases p21350_3 (m.d 0 3) (by simp) with h21383 | h21383
            · rcases p21350_3 (m.d 0 4) (by simp) with h21384 | h21384
              · rcases p21350_3 (m.d 0 5) (by simp) with h21385 | h21385
                · linarith only [h20413, h21385, hlam]
                · linarith only [h18815, h21385, hlam]
              · linarith only [h16915, h21384, hlam]
            · linarith only [h14396, h21383, hlam]
          · linarith only [h0, h21382, hlam]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h20409, hlam, p21350_0]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h20411, hlam, p21350_0]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [hlam, p21350_0]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h20413, h20420, h20421, h21348, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p21350_1]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        rcases p21350_3 (m.d 0 1) (by simp) with h21395 | h21395
        · linarith only [h18815, h21395, hlam]
        · rcases p21350_3 (m.d 0 2) (by simp) with h21397 | h21397
          · rcases p21350_3 (m.d 0 3) (by simp) with h21398 | h21398
            · rcases p21350_3 (m.d 0 4) (by simp) with h21399 | h21399
              · rcases p21350_3 (m.d 0 5) (by simp) with h21400 | h21400
                · rcases h2bigk with h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h0, hlam, p21401_1]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    rcases p21401_3 (m.d 0 2) (by simp) with h21404 | h21404
                    · rcases p21401_3 (m.d 1 2) (by simp) with h21405 | h21405
                      · rcases p21401_3 (m.d 2 3) (by simp) with h21406 | h21406
                        · linarith only [h21406, hlam, p21401_0]
                        · rcases p21401_3 (m.d 2 4) (by simp) with h21408 | h21408
                          · linarith only [h20409, h21408, hlam]
                          · rcases p21401_3 (m.d 2 5) (by simp) with h21410 | h21410
                            · linarith only [h20410, h21410, hlam]
                            · linarith only [h20421, h21410, hlam]
                      · linarith only [h20414, h21405, hlam]
                    · linarith only [h21404, hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    rcases p21401_3 (m.d 0 2) (by simp) with h21415 | h21415
                    · rcases p21401_3 (m.d 1 2) (by simp) with h21416 | h21416
                      · rcases p21401_3 (m.d 2 3) (by simp) with h21417 | h21417
                        · linarith only [h20408, h21417, hlam]
                        · linarith only [h20420, h21417, hlam]
                      · linarith only [h20415, h21416, hlam]
                    · linarith only [h21415, hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    rcases p21401_3 (m.d 0 2) (by simp) with h21422 | h21422
                    · rcases p21401_3 (m.d 1 2) (by simp) with h21423 | h21423
                      · rcases p21401_3 (m.d 2 3) (by simp) with h21424 | h21424
                        · linarith only [h20408, h21424, hlam]
                        · rcases p21401_3 (m.d 2 4) (by simp) with h21426 | h21426
                          · linarith only [h20409, h21426, hlam]
                          · rcases p21401_3 (m.d 2 5) (by simp) with h21428 | h21428
                            · linarith only [h21428, hlam, p21401_0]
                            · rcases h3bigk with h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c | h21430c
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h14396, hlam, p21430_1]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h14396, h20414, h20420, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21430_1]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                rcases p21430_3 (m.d 0 3) (by simp) with h21434 | h21434
                                · rcases p21430_3 (m.d 1 3) (by simp) with h21435 | h21435
                                  · rcases p21430_3 (m.d 2 3) (by simp) with h21436 | h21436
                                    · linarith only [h20408, h21436, hlam]
                                    · linarith only [h20420, h21436, hlam]
                                  · linarith only [h20417, h21435, hlam]
                                · linarith only [h21434, hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h14396, h20414, h20420, h20421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21430_1]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p21430_1]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h20414, h20420, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21430_1]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                rcases p21430_3 (m.d 0 3) (by simp) with h21445 | h21445
                                · linarith only [h14396, h21445, hlam]
                                · linarith only [h20411, h21445, hlam]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h20414, h20420, h20421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21430_1]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h20408, hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h20414, hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h20421, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p21430_1]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h20421, hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h20411, hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h20417, hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h20420, hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h21348, hlam, p21430_1]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h20412, hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h20418, hlam, p21430_0]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [hc23, hc35, hlam, hphi, p21430_1]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [h16915, h20413, h20414, h20417, h21348, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21430_1]
                              · have p21430_0 := h21430c.1
                                have p21430_1 := h21430c.2.1
                                have p21430_2 := h21430c.2.2.1
                                have p21430_3 := h21430c.2.2.2
                                linarith only [hlam, p21430_0]
                      · linarith only [h20416, h21423, hlam]
                    · linarith only [h21422, hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h20410, hc01, hc12, hlam, hphi, p21350_1, p21401_1]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    rcases p21401_3 (m.d 0 2) (by simp) with h21468 | h21468
                    · linarith only [h0, h21468, hlam]
                    · linarith only [h20408, h21468, hlam]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    rcases p21401_3 (m.d 0 2) (by simp) with h21471 | h21471
                    · linarith only [h0, h21471, hlam]
                    · linarith only [h20409, h21471, hlam]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    rcases p21401_3 (m.d 0 2) (by simp) with h21474 | h21474
                    · linarith only [h0, h21474, hlam]
                    · linarith only [h20410, h21474, hlam]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h20408, hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h20414, hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h20408, h20411, h20413, h20421, h21348, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p21401_1]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h20421, hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h20409, hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h20415, hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h20420, hlam, p21401_1]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h21346, hlam, p21401_1]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h20410, hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h20416, hlam, p21401_0]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [h0, h20410, h20420, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21401_1]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    rcases p21401_3 (m.d 0 2) (by simp) with h21490 | h21490
                    · rcases p21401_3 (m.d 1 2) (by simp) with h21491 | h21491
                      · rcases p21401_3 (m.d 2 3) (by simp) with h21492 | h21492
                        · linarith only [h20421, h21492, hlam]
                        · linarith only [h20420, h21492, hlam]
                      · linarith only [h20415, h21491, hlam]
                    · linarith only [h20409, h21490, hlam]
                  · have p21401_0 := h21401c.1
                    have p21401_1 := h21401c.2.1
                    have p21401_2 := h21401c.2.2.1
                    have p21401_3 := h21401c.2.2.2
                    linarith only [hlam, p21401_0]
                · linarith only [h18815, h21400, hlam]
              · linarith only [h16915, h21399, hlam]
            · linarith only [h14396, h21398, hlam]
          · linarith only [h0, h21397, hlam]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h20410, hlam, p21350_1]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h20412, hlam, p21350_0]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [h20413, hlam, p21350_1]
      · have p21350_0 := h21350c.1
        have p21350_1 := h21350c.2.1
        have p21350_2 := h21350c.2.2.1
        have p21350_3 := h21350c.2.2.2
        linarith only [hlam, p21350_0]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20419 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h20420 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 2 3 5 (by decide) (by decide) with h20421 | h20421
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418 h20419 h20420 h20421
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418 h20419 h20420 h20421

end R2N4
