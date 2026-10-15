import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x0 (m : N7Model)
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
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
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
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  rcases h1bigk with h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    rcases p919_3 (m.d 0 1) (by simp) with h921 | h921
    · rcases p919_3 (m.d 1 2) (by simp) with h922 | h922
      · linarith only [h922, hlam, p919_0]
      · rcases p919_3 (m.d 1 3) (by simp) with h924 | h924
        · linarith only [h1, h924, hlam]
        · rcases p919_3 (m.d 1 4) (by simp) with h926 | h926
          · linarith only [h2, h926, hlam]
          · rcases p919_3 (m.d 1 5) (by simp) with h928 | h928
            · linarith only [h3, h928, hlam]
            · rcases h1emax with h930 | h930 | h930 | h930 | h930
              · linarith only [h930, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p919_1]
              · rcases h2bigk with h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [hlam, p932_0]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  rcases p932_3 (m.d 0 2) (by simp) with h934 | h934
                  · rcases p932_3 (m.d 1 2) (by simp) with h935 | h935
                    · linarith only [h0, h935, hlam]
                    · rcases p932_3 (m.d 2 3) (by simp) with h937 | h937
                      · linarith only [h4, h937, hlam]
                      · rcases p932_3 (m.d 2 4) (by simp) with h939 | h939
                        · linarith only [h5, h939, hlam]
                        · rcases p932_3 (m.d 2 5) (by simp) with h941 | h941
                          · linarith only [h6, h941, hlam]
                          · rcases h4bigk with h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              rcases p943_3 (m.d 0 4) (by simp) with h945 | h945
                              · rcases p943_3 (m.d 1 4) (by simp) with h946 | h946
                                · linarith only [h2, h946, hlam]
                                · rcases p943_3 (m.d 2 4) (by simp) with h948 | h948
                                  · linarith only [h5, h948, hlam]
                                  · rcases p943_3 (m.d 3 4) (by simp) with h950 | h950
                                    · linarith only [h7, h950, hlam]
                                    · linarith only [h13, h950, hlam]
                              · linarith only [h2, h945, hlam]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              rcases p943_3 (m.d 0 4) (by simp) with h954 | h954
                              · rcases p943_3 (m.d 1 4) (by simp) with h955 | h955
                                · linarith only [h2, h955, hlam]
                                · linarith only [h11, h955, hlam]
                              · linarith only [h5, h954, hlam]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h10, h13, h498, h918, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p943_1]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              rcases p943_3 (m.d 0 4) (by simp) with h960 | h960
                              · rcases p943_3 (m.d 1 4) (by simp) with h961 | h961
                                · linarith only [h2, h961, hlam]
                                · rcases p943_3 (m.d 2 4) (by simp) with h963 | h963
                                  · linarith only [h5, h963, hlam]
                                  · rcases p943_3 (m.d 3 4) (by simp) with h965 | h965
                                    · linarith only [h7, h965, hlam]
                                    · linarith only [h918, h965, hlam]
                              · linarith only [h960, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h2, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h498, h912, h918, hc23, hc34, hlam, hphi, p943_1]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h13, hlam, p943_1]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h498, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h5, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h11, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h912, hlam, p943_1]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h916, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h7, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              rcases p943_3 (m.d 0 4) (by simp) with h980 | h980
                              · rcases p943_3 (m.d 1 4) (by simp) with h981 | h981
                                · linarith only [h13, h981, hlam]
                                · rcases p943_3 (m.d 2 4) (by simp) with h983 | h983
                                  · linarith only [h912, h983, hlam]
                                  · rcases p943_3 (m.d 3 4) (by simp) with h985 | h985
                                    · rcases p943_3 (m.d 4 5) (by simp) with h986 | h986
                                      · linarith only [h918, h986, hlam]
                                      · linarith only [h498, h986, hlam]
                                    · linarith only [h13, h985, hlam]
                              · linarith only [h2, h980, hlam]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              rcases p943_3 (m.d 0 4) (by simp) with h991 | h991
                              · rcases p943_3 (m.d 1 4) (by simp) with h992 | h992
                                · linarith only [h13, h992, hlam]
                                · linarith only [h11, h992, hlam]
                              · linarith only [h5, h991, hlam]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h0, h4, h498, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p943_1]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h9, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h0, h11, h4, h7, h912, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p943_1]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h0, h4, h7, h912, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p943_1]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h918, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [hlam, p943_0]
                  · linarith only [h0, h934, hlam]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h11, h4, h498, h7, h912, h918, hlam, p932_2]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h11, h4, h498, h7, h918, hlam, p932_2]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  rcases p932_3 (m.d 0 2) (by simp) with h1006 | h1006
                  · rcases p932_3 (m.d 1 2) (by simp) with h1007 | h1007
                    · linarith only [h0, h1007, hlam]
                    · linarith only [h1007, h12, hlam]
                  · linarith only [h1006, hlam, p932_0]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h0, hlam, p932_1]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [hlam, p932_0]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h930, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p932_1]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h930, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p932_1]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h930, hc25, hlam, hphi, ht01, ht0b, ht5b, p932_1]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h4, hlam, p932_0]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h10, hlam, p932_0]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [hlam, p932_0]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h912, hlam, p932_1]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h914, hlam, p932_1]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h5, hlam, p932_0]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h11, hlam, p932_0]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h11, h930, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p932_1]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [hlam, p932_0]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h916, hlam, p932_0]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h6, hlam, p932_0]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h12, hlam, p932_0]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h12, h930, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p932_1]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [h12, h930, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p932_1]
                · have p932_0 := h932c.1
                  have p932_1 := h932c.2.1
                  have p932_2 := h932c.2.2.1
                  have p932_3 := h932c.2.2.2
                  linarith only [hlam, p932_0]
              · rcases h2bigk with h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [hlam, p1031_0]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  rcases p1031_3 (m.d 0 2) (by simp) with h1033 | h1033
                  · rcases p1031_3 (m.d 1 2) (by simp) with h1034 | h1034
                    · linarith only [h0, h1034, hlam]
                    · rcases p1031_3 (m.d 2 3) (by simp) with h1036 | h1036
                      · linarith only [h1036, h4, hlam]
                      · rcases p1031_3 (m.d 2 4) (by simp) with h1038 | h1038
                        · linarith only [h1038, h5, hlam]
                        · rcases p1031_3 (m.d 2 5) (by simp) with h1040 | h1040
                          · linarith only [h1040, h6, hlam]
                          · rcases h4bigk with h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              rcases p1042_3 (m.d 0 4) (by simp) with h1044 | h1044
                              · rcases p1042_3 (m.d 1 4) (by simp) with h1045 | h1045
                                · linarith only [h1045, h2, hlam]
                                · rcases p1042_3 (m.d 2 4) (by simp) with h1047 | h1047
                                  · linarith only [h1047, h5, hlam]
                                  · rcases p1042_3 (m.d 3 4) (by simp) with h1049 | h1049
                                    · linarith only [h1049, h7, hlam]
                                    · linarith only [h1049, h13, hlam]
                              · linarith only [h1044, h2, hlam]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              rcases p1042_3 (m.d 0 4) (by simp) with h1053 | h1053
                              · rcases p1042_3 (m.d 1 4) (by simp) with h1054 | h1054
                                · linarith only [h1054, h2, hlam]
                                · linarith only [h1054, h11, hlam]
                              · linarith only [h1053, h5, hlam]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h10, h13, h498, h918, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              rcases p1042_3 (m.d 0 4) (by simp) with h1059 | h1059
                              · rcases p1042_3 (m.d 1 4) (by simp) with h1060 | h1060
                                · linarith only [h1060, h2, hlam]
                                · rcases p1042_3 (m.d 2 4) (by simp) with h1062 | h1062
                                  · linarith only [h1062, h5, hlam]
                                  · rcases p1042_3 (m.d 3 4) (by simp) with h1064 | h1064
                                    · linarith only [h1064, h7, hlam]
                                    · linarith only [h1064, h918, hlam]
                              · linarith only [h1059, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h2, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h498, h918, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h13, hlam, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h498, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h5, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h11, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h912, hlam, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h916, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h7, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              rcases p1042_3 (m.d 0 4) (by simp) with h1079 | h1079
                              · rcases p1042_3 (m.d 1 4) (by simp) with h1080 | h1080
                                · linarith only [h1080, h13, hlam]
                                · rcases p1042_3 (m.d 2 4) (by simp) with h1082 | h1082
                                  · linarith only [h1082, h912, hlam]
                                  · rcases p1042_3 (m.d 3 4) (by simp) with h1084 | h1084
                                    · rcases p1042_3 (m.d 4 5) (by simp) with h1085 | h1085
                                      · linarith only [h1085, h918, hlam]
                                      · linarith only [h1085, h498, hlam]
                                    · linarith only [h1084, h13, hlam]
                              · linarith only [h1079, h2, hlam]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              rcases p1042_3 (m.d 0 4) (by simp) with h1090 | h1090
                              · rcases p1042_3 (m.d 1 4) (by simp) with h1091 | h1091
                                · linarith only [h1091, h13, hlam]
                                · linarith only [h1091, h11, hlam]
                              · linarith only [h1090, h5, hlam]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h0, h10, h13, h4, h498, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h9, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h0, h10, h13, h4, h7, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h0, h4, h7, h912, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h918, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [hlam, p1042_0]
                  · linarith only [h0, h1033, hlam]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h10, h13, h4, h498, h7, h918, hlam, p1031_2]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h11, h4, h498, h7, h918, hlam, p1031_2]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  rcases p1031_3 (m.d 0 2) (by simp) with h1105 | h1105
                  · rcases p1031_3 (m.d 1 2) (by simp) with h1106 | h1106
                    · linarith only [h0, h1106, hlam]
                    · linarith only [h1106, h12, hlam]
                  · linarith only [h1105, hlam, p1031_0]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h0, hlam, p1031_1]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [hlam, p1031_0]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1031_1, p919_1]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1031_1, p919_1]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [hc01, hc25, hlam, hphi, ht0b, ht5b, p1031_1, p919_1]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h4, hlam, p1031_0]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h10, hlam, p1031_0]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [hlam, p1031_0]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h912, hlam, p1031_1]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h914, hlam, p1031_1]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h5, hlam, p1031_0]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h11, hlam, p1031_0]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1031_1, p919_1]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [hlam, p1031_0]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h916, hlam, p1031_0]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h6, hlam, p1031_0]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h12, hlam, p1031_0]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1031_1, p919_1]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1031_1, p919_1]
                · have p1031_0 := h1031c.1
                  have p1031_1 := h1031c.2.1
                  have p1031_2 := h1031c.2.2.1
                  have p1031_3 := h1031c.2.2.2
                  linarith only [hlam, p1031_0]
              · rcases h2bigk with h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [hlam, p1130_0]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  rcases p1130_3 (m.d 0 2) (by simp) with h1132 | h1132
                  · rcases p1130_3 (m.d 1 2) (by simp) with h1133 | h1133
                    · linarith only [h0, h1133, hlam]
                    · rcases p1130_3 (m.d 2 3) (by simp) with h1135 | h1135
                      · linarith only [h1135, h4, hlam]
                      · rcases p1130_3 (m.d 2 4) (by simp) with h1137 | h1137
                        · linarith only [h1137, h5, hlam]
                        · rcases p1130_3 (m.d 2 5) (by simp) with h1139 | h1139
                          · linarith only [h1139, h6, hlam]
                          · rcases h4bigk with h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              rcases p1141_3 (m.d 0 4) (by simp) with h1143 | h1143
                              · rcases p1141_3 (m.d 1 4) (by simp) with h1144 | h1144
                                · linarith only [h1144, h2, hlam]
                                · rcases p1141_3 (m.d 2 4) (by simp) with h1146 | h1146
                                  · linarith only [h1146, h5, hlam]
                                  · rcases p1141_3 (m.d 3 4) (by simp) with h1148 | h1148
                                    · linarith only [h1148, h7, hlam]
                                    · linarith only [h1148, h13, hlam]
                              · linarith only [h1143, h2, hlam]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              rcases p1141_3 (m.d 0 4) (by simp) with h1152 | h1152
                              · rcases p1141_3 (m.d 1 4) (by simp) with h1153 | h1153
                                · linarith only [h1153, h2, hlam]
                                · linarith only [h11, h1153, hlam]
                              · linarith only [h1152, h5, hlam]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h13, h498, h918, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1141_1]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              rcases p1141_3 (m.d 0 4) (by simp) with h1158 | h1158
                              · rcases p1141_3 (m.d 1 4) (by simp) with h1159 | h1159
                                · linarith only [h1159, h2, hlam]
                                · rcases p1141_3 (m.d 2 4) (by simp) with h1161 | h1161
                                  · linarith only [h1161, h5, hlam]
                                  · rcases p1141_3 (m.d 3 4) (by simp) with h1163 | h1163
                                    · linarith only [h1163, h7, hlam]
                                    · linarith only [h1163, h918, hlam]
                              · linarith only [h1158, hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h2, hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h498, h918, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1141_1]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h13, hlam, p1141_1]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h498, hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h5, hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h11, hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h912, hlam, p1141_1]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h916, hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h7, hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              rcases p1141_3 (m.d 0 4) (by simp) with h1178 | h1178
                              · rcases p1141_3 (m.d 1 4) (by simp) with h1179 | h1179
                                · linarith only [h1179, h13, hlam]
                                · rcases p1141_3 (m.d 2 4) (by simp) with h1181 | h1181
                                  · linarith only [h1181, h912, hlam]
                                  · rcases p1141_3 (m.d 3 4) (by simp) with h1183 | h1183
                                    · rcases p1141_3 (m.d 4 5) (by simp) with h1184 | h1184
                                      · linarith only [h1184, h918, hlam]
                                      · linarith only [h1184, h498, hlam]
                                    · linarith only [h1183, h13, hlam]
                              · linarith only [h1178, h2, hlam]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              rcases p1141_3 (m.d 0 4) (by simp) with h1189 | h1189
                              · rcases p1141_3 (m.d 1 4) (by simp) with h1190 | h1190
                                · linarith only [h1190, h13, hlam]
                                · linarith only [h11, h1190, hlam]
                              · linarith only [h1189, h5, hlam]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h0, h13, h4, h498, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1141_1]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h9, hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h0, h10, h13, h4, h7, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1141_1]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h0, h4, h7, h912, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1141_1]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [h918, hlam, p1141_0]
                            · have p1141_0 := h1141c.1
                              have p1141_1 := h1141c.2.1
                              have p1141_2 := h1141c.2.2.1
                              have p1141_3 := h1141c.2.2.2
                              linarith only [hlam, p1141_0]
                  · linarith only [h0, h1132, hlam]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h10, h13, h4, h498, h7, h918, hlam, p1130_2]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h11, h4, h498, h7, h918, hlam, p1130_2]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  rcases p1130_3 (m.d 0 2) (by simp) with h1204 | h1204
                  · rcases p1130_3 (m.d 1 2) (by simp) with h1205 | h1205
                    · linarith only [h0, h1205, hlam]
                    · linarith only [h12, h1205, hlam]
                  · linarith only [h1204, hlam, p1130_0]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h0, hlam, p1130_1]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [hlam, p1130_0]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1130_1, p919_1]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1130_1, p919_1]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [hc01, hc25, hlam, hphi, ht0b, ht5b, p1130_1, p919_1]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h4, hlam, p1130_0]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h10, hlam, p1130_0]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [hlam, p1130_0]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h912, hlam, p1130_1]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h914, hlam, p1130_1]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h5, hlam, p1130_0]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h11, hlam, p1130_0]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1130_1, p919_1]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [hlam, p1130_0]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h916, hlam, p1130_0]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h6, hlam, p1130_0]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h12, hlam, p1130_0]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1130_1, p919_1]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1130_1, p919_1]
                · have p1130_0 := h1130c.1
                  have p1130_1 := h1130c.2.1
                  have p1130_2 := h1130c.2.2.1
                  have p1130_3 := h1130c.2.2.2
                  linarith only [hlam, p1130_0]
              · rcases h2bigk with h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [hlam, p1229_0]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  rcases p1229_3 (m.d 0 2) (by simp) with h1231 | h1231
                  · rcases p1229_3 (m.d 1 2) (by simp) with h1232 | h1232
                    · linarith only [h0, h1232, hlam]
                    · rcases p1229_3 (m.d 2 3) (by simp) with h1234 | h1234
                      · linarith only [h1234, h4, hlam]
                      · rcases p1229_3 (m.d 2 4) (by simp) with h1236 | h1236
                        · linarith only [h1236, h5, hlam]
                        · rcases p1229_3 (m.d 2 5) (by simp) with h1238 | h1238
                          · linarith only [h1238, h6, hlam]
                          · rcases h4bigk with h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              rcases p1240_3 (m.d 0 4) (by simp) with h1242 | h1242
                              · rcases p1240_3 (m.d 1 4) (by simp) with h1243 | h1243
                                · linarith only [h1243, h2, hlam]
                                · rcases p1240_3 (m.d 2 4) (by simp) with h1245 | h1245
                                  · linarith only [h1245, h5, hlam]
                                  · rcases p1240_3 (m.d 3 4) (by simp) with h1247 | h1247
                                    · linarith only [h1247, h7, hlam]
                                    · linarith only [h1247, h13, hlam]
                              · linarith only [h1242, h2, hlam]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              rcases p1240_3 (m.d 0 4) (by simp) with h1251 | h1251
                              · rcases p1240_3 (m.d 1 4) (by simp) with h1252 | h1252
                                · linarith only [h1252, h2, hlam]
                                · linarith only [h11, h1252, hlam]
                              · linarith only [h1251, h5, hlam]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h13, h498, h918, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1240_1]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              rcases p1240_3 (m.d 0 4) (by simp) with h1257 | h1257
                              · rcases p1240_3 (m.d 1 4) (by simp) with h1258 | h1258
                                · linarith only [h1258, h2, hlam]
                                · rcases p1240_3 (m.d 2 4) (by simp) with h1260 | h1260
                                  · linarith only [h1260, h5, hlam]
                                  · rcases p1240_3 (m.d 3 4) (by simp) with h1262 | h1262
                                    · linarith only [h1262, h7, hlam]
                                    · linarith only [h1262, h918, hlam]
                              · linarith only [h1257, hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h2, hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h498, h918, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1240_1]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h13, hlam, p1240_1]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h498, hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h5, hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h11, hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h912, hlam, p1240_1]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h916, hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h7, hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              rcases p1240_3 (m.d 0 4) (by simp) with h1277 | h1277
                              · rcases p1240_3 (m.d 1 4) (by simp) with h1278 | h1278
                                · linarith only [h1278, h13, hlam]
                                · rcases p1240_3 (m.d 2 4) (by simp) with h1280 | h1280
                                  · linarith only [h1280, h912, hlam]
                                  · rcases p1240_3 (m.d 3 4) (by simp) with h1282 | h1282
                                    · rcases p1240_3 (m.d 4 5) (by simp) with h1283 | h1283
                                      · linarith only [h1283, h918, hlam]
                                      · linarith only [h1283, h498, hlam]
                                    · linarith only [h1282, h13, hlam]
                              · linarith only [h1277, h2, hlam]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              rcases p1240_3 (m.d 0 4) (by simp) with h1288 | h1288
                              · rcases p1240_3 (m.d 1 4) (by simp) with h1289 | h1289
                                · linarith only [h1289, h13, hlam]
                                · linarith only [h11, h1289, hlam]
                              · linarith only [h1288, h5, hlam]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h0, h13, h4, h498, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1240_1]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h9, hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h0, h10, h13, h4, h7, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1240_1]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h0, h4, h7, h912, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1240_1]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [h918, hlam, p1240_0]
                            · have p1240_0 := h1240c.1
                              have p1240_1 := h1240c.2.1
                              have p1240_2 := h1240c.2.2.1
                              have p1240_3 := h1240c.2.2.2
                              linarith only [hlam, p1240_0]
                  · linarith only [h0, h1231, hlam]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h10, h13, h4, h498, h7, h918, hlam, p1229_2]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h11, h4, h498, h7, h918, hlam, p1229_2]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  rcases p1229_3 (m.d 0 2) (by simp) with h1303 | h1303
                  · rcases p1229_3 (m.d 1 2) (by simp) with h1304 | h1304
                    · linarith only [h0, h1304, hlam]
                    · linarith only [h12, h1304, hlam]
                  · linarith only [h1303, hlam, p1229_0]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h0, hlam, p1229_1]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [hlam, p1229_0]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1229_1, p919_1]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1229_1, p919_1]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [hc01, hc25, hlam, hphi, ht0b, ht5b, p1229_1, p919_1]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h4, hlam, p1229_0]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h10, hlam, p1229_0]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [hlam, p1229_0]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h912, hlam, p1229_1]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h914, hlam, p1229_1]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h5, hlam, p1229_0]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h11, hlam, p1229_0]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1229_1, p919_1]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [hlam, p1229_0]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h916, hlam, p1229_0]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h6, hlam, p1229_0]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h12, hlam, p1229_0]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1229_1, p919_1]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1229_1, p919_1]
                · have p1229_0 := h1229c.1
                  have p1229_1 := h1229c.2.1
                  have p1229_2 := h1229c.2.2.1
                  have p1229_3 := h1229c.2.2.2
                  linarith only [hlam, p1229_0]
    · linarith only [h921, hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h0, h13, h4, h498, h7, h918, hlam, p919_2]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h0, h4, h498, h7, h918, hlam, p919_2]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    rcases p919_3 (m.d 0 1) (by simp) with h1331 | h1331
    · rcases p919_3 (m.d 1 2) (by simp) with h1332 | h1332
      · linarith only [h0, h1332, hlam]
      · linarith only [h12, h1332, hlam]
    · linarith only [h1331, hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h0, hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    rcases p919_3 (m.d 0 1) (by simp) with h1338 | h1338
    · rcases p919_3 (m.d 1 2) (by simp) with h1339 | h1339
      · rcases p919_3 (m.d 1 3) (by simp) with h1340 | h1340
        · linarith only [h10, h1340, hlam]
        · rcases p919_3 (m.d 1 4) (by simp) with h1342 | h1342
          · linarith only [h11, h1342, hlam]
          · linarith only [h13, h1342, hlam]
      · linarith only [h10, h1339, hlam]
    · linarith only [h1, h1338, hlam]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    rcases p919_3 (m.d 0 1) (by simp) with h1347 | h1347
    · rcases p919_3 (m.d 1 2) (by simp) with h1348 | h1348
      · rcases p919_3 (m.d 1 3) (by simp) with h1349 | h1349
        · linarith only [h10, h1349, hlam]
        · rcases p919_3 (m.d 1 4) (by simp) with h1351 | h1351
          · linarith only [h11, h1351, hlam]
          · rcases p919_3 (m.d 1 5) (by simp) with h1353 | h1353
            · linarith only [h12, h1353, hlam]
            · linarith only [h1353, h498, hlam]
      · linarith only [h11, h1348, hlam]
    · linarith only [h1347, h2, hlam]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    rcases p919_3 (m.d 0 1) (by simp) with h1358 | h1358
    · rcases p919_3 (m.d 1 2) (by simp) with h1359 | h1359
      · rcases p919_3 (m.d 1 3) (by simp) with h1360 | h1360
        · linarith only [h10, h1360, hlam]
        · rcases p919_3 (m.d 1 4) (by simp) with h1362 | h1362
          · linarith only [h11, h1362, hlam]
          · rcases p919_3 (m.d 1 5) (by simp) with h1364 | h1364
            · linarith only [h12, h1364, hlam]
            · rcases h1emax with h1366 | h1366 | h1366 | h1366 | h1366
              · linarith only [h0, h1366, h4, h7, h918, hc45, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h11, h1366, h498, h912, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p919_1]
              · rcases h2bigk with h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [hlam, p1369_0]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h0, h11, h498, h912, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1369_1, p919_1]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h11, h4, h498, h7, h912, h918, hlam, p1369_2]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h11, h4, h498, h7, h918, hlam, p1369_2]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  rcases p1369_3 (m.d 0 2) (by simp) with h1374 | h1374
                  · rcases p1369_3 (m.d 1 2) (by simp) with h1375 | h1375
                    · linarith only [h0, h1375, hlam]
                    · linarith only [h12, h1375, hlam]
                  · linarith only [h1374, hlam, p1369_0]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h0, hlam, p1369_1]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [hlam, p1369_0]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  rcases p1369_3 (m.d 0 2) (by simp) with h1381 | h1381
                  · rcases p1369_3 (m.d 1 2) (by simp) with h1382 | h1382
                    · rcases p1369_3 (m.d 2 3) (by simp) with h1383 | h1383
                      · linarith only [h1383, hlam, p1369_0]
                      · rcases p1369_3 (m.d 2 4) (by simp) with h1385 | h1385
                        · linarith only [h11, h1385, hlam]
                        · linarith only [h1385, h912, hlam]
                    · linarith only [h1382, hlam, p1369_0]
                  · linarith only [h1381, h4, hlam]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  rcases p1369_3 (m.d 0 2) (by simp) with h1390 | h1390
                  · rcases p1369_3 (m.d 1 2) (by simp) with h1391 | h1391
                    · rcases p1369_3 (m.d 2 3) (by simp) with h1392 | h1392
                      · linarith only [h10, h1392, hlam]
                      · rcases p1369_3 (m.d 2 4) (by simp) with h1394 | h1394
                        · linarith only [h1394, hlam, p1369_0]
                        · rcases p1369_3 (m.d 2 5) (by simp) with h1396 | h1396
                          · linarith only [h12, h1396, hlam]
                          · linarith only [h1396, h916, hlam]
                    · linarith only [h1391, hlam, p1369_0]
                  · linarith only [h1390, h5, hlam]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  rcases p1369_3 (m.d 0 2) (by simp) with h1401 | h1401
                  · rcases p1369_3 (m.d 1 2) (by simp) with h1402 | h1402
                    · rcases p1369_3 (m.d 2 3) (by simp) with h1403 | h1403
                      · linarith only [h10, h1403, hlam]
                      · rcases p1369_3 (m.d 2 4) (by simp) with h1405 | h1405
                        · linarith only [h11, h1405, hlam]
                        · rcases p1369_3 (m.d 2 5) (by simp) with h1407 | h1407
                          · linarith only [h1407, hlam, p1369_0]
                          · rcases h4bigk with h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              rcases p1409_3 (m.d 0 4) (by simp) with h1411 | h1411
                              · rcases p1409_3 (m.d 1 4) (by simp) with h1412 | h1412
                                · linarith only [h1412, h2, hlam]
                                · rcases p1409_3 (m.d 2 4) (by simp) with h1414 | h1414
                                  · linarith only [h1414, h5, hlam]
                                  · rcases p1409_3 (m.d 3 4) (by simp) with h1416 | h1416
                                    · linarith only [h1416, h7, hlam]
                                    · linarith only [h13, h1416, hlam]
                              · linarith only [h1411, h2, hlam]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              rcases p1409_3 (m.d 0 4) (by simp) with h1420 | h1420
                              · rcases p1409_3 (m.d 1 4) (by simp) with h1421 | h1421
                                · linarith only [h1421, h2, hlam]
                                · linarith only [h11, h1421, hlam]
                              · linarith only [h1420, h5, hlam]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h11, h498, h912, h918, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1409_1]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              rcases p1409_3 (m.d 0 4) (by simp) with h1426 | h1426
                              · rcases p1409_3 (m.d 1 4) (by simp) with h1427 | h1427
                                · linarith only [h1427, h2, hlam]
                                · rcases p1409_3 (m.d 2 4) (by simp) with h1429 | h1429
                                  · linarith only [h1429, h5, hlam]
                                  · rcases p1409_3 (m.d 3 4) (by simp) with h1431 | h1431
                                    · linarith only [h1431, h7, hlam]
                                    · linarith only [h1431, h918, hlam]
                              · linarith only [h1426, hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h2, hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h498, h912, h918, hc23, hc34, hlam, hphi, p1409_1]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h13, hlam, p1409_1]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h498, hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h5, hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h11, hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h912, hlam, p1409_1]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h916, hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h7, hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              rcases p1409_3 (m.d 0 4) (by simp) with h1446 | h1446
                              · rcases p1409_3 (m.d 1 4) (by simp) with h1447 | h1447
                                · linarith only [h13, h1447, hlam]
                                · rcases p1409_3 (m.d 2 4) (by simp) with h1449 | h1449
                                  · linarith only [h1449, h912, hlam]
                                  · rcases p1409_3 (m.d 3 4) (by simp) with h1451 | h1451
                                    · rcases p1409_3 (m.d 4 5) (by simp) with h1452 | h1452
                                      · linarith only [h1452, h918, hlam]
                                      · linarith only [h1452, h498, hlam]
                                    · linarith only [h13, h1451, hlam]
                              · linarith only [h1446, h2, hlam]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              rcases p1409_3 (m.d 0 4) (by simp) with h1457 | h1457
                              · rcases p1409_3 (m.d 1 4) (by simp) with h1458 | h1458
                                · linarith only [h13, h1458, hlam]
                                · linarith only [h11, h1458, hlam]
                              · linarith only [h1457, h5, hlam]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h0, h4, h498, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1409_1]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h9, hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h0, h11, h4, h7, h912, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1409_1]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h0, h4, h7, h912, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1409_1]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [h918, hlam, p1409_0]
                            · have p1409_0 := h1409c.1
                              have p1409_1 := h1409c.2.1
                              have p1409_2 := h1409c.2.2.1
                              have p1409_3 := h1409c.2.2.2
                              linarith only [hlam, p1409_0]
                    · linarith only [h1402, hlam, p1369_0]
                  · linarith only [h1401, h6, hlam]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h4, hlam, p1369_0]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h10, hlam, p1369_0]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [hlam, p1369_0]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h912, hlam, p1369_1]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h914, hlam, p1369_1]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h5, hlam, p1369_0]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h11, hlam, p1369_0]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1369_1]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [hlam, p1369_0]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h916, hlam, p1369_0]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h6, hlam, p1369_0]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h12, hlam, p1369_0]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1369_1, p919_1]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [h0, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1369_1, p919_1]
                · have p1369_0 := h1369c.1
                  have p1369_1 := h1369c.2.1
                  have p1369_2 := h1369c.2.2.1
                  have p1369_3 := h1369c.2.2.2
                  linarith only [hlam, p1369_0]
              · rcases h2bigk with h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c | h1486c
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [hlam, p1486_0]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p1486_1, p919_1]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h11, h4, h498, h7, h912, h918, hlam, p1486_2]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h11, h4, h498, h7, h918, hlam, p1486_2]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  rcases p1486_3 (m.d 0 2) (by simp) with h1491 | h1491
                  · rcases p1486_3 (m.d 1 2) (by simp) with h1492 | h1492
                    · linarith only [h0, h1492, hlam]
                    · linarith only [h12, h1492, hlam]
                  · linarith only [h1491, hlam, p1486_0]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h0, hlam, p1486_1]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [hlam, p1486_0]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  rcases p1486_3 (m.d 0 2) (by simp) with h1498 | h1498
                  · rcases p1486_3 (m.d 1 2) (by simp) with h1499 | h1499
                    · rcases p1486_3 (m.d 2 3) (by simp) with h1500 | h1500
                      · linarith only [h1500, hlam, p1486_0]
                      · rcases p1486_3 (m.d 2 4) (by simp) with h1502 | h1502
                        · linarith only [h11, h1502, hlam]
                        · linarith only [h1502, h912, hlam]
                    · linarith only [h1499, hlam, p1486_0]
                  · linarith only [h1498, h4, hlam]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  rcases p1486_3 (m.d 0 2) (by simp) with h1507 | h1507
                  · rcases p1486_3 (m.d 1 2) (by simp) with h1508 | h1508
                    · rcases p1486_3 (m.d 2 3) (by simp) with h1509 | h1509
                      · linarith only [h10, h1509, hlam]
                      · rcases p1486_3 (m.d 2 4) (by simp) with h1511 | h1511
                        · linarith only [h1511, hlam, p1486_0]
                        · rcases p1486_3 (m.d 2 5) (by simp) with h1513 | h1513
                          · linarith only [h12, h1513, hlam]
                          · linarith only [h1513, h916, hlam]
                    · linarith only [h1508, hlam, p1486_0]
                  · linarith only [h1507, h5, hlam]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  rcases p1486_3 (m.d 0 2) (by simp) with h1518 | h1518
                  · rcases p1486_3 (m.d 1 2) (by simp) with h1519 | h1519
                    · rcases p1486_3 (m.d 2 3) (by simp) with h1520 | h1520
                      · linarith only [h10, h1520, hlam]
                      · rcases p1486_3 (m.d 2 4) (by simp) with h1522 | h1522
                        · linarith only [h11, h1522, hlam]
                        · rcases p1486_3 (m.d 2 5) (by simp) with h1524 | h1524
                          · linarith only [h1524, hlam, p1486_0]
                          · rcases h4bigk with h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              rcases p1526_3 (m.d 0 4) (by simp) with h1528 | h1528
                              · rcases p1526_3 (m.d 1 4) (by simp) with h1529 | h1529
                                · linarith only [h1529, h2, hlam]
                                · rcases p1526_3 (m.d 2 4) (by simp) with h1531 | h1531
                                  · linarith only [h1531, h5, hlam]
                                  · rcases p1526_3 (m.d 3 4) (by simp) with h1533 | h1533
                                    · linarith only [h1533, h7, hlam]
                                    · linarith only [h13, h1533, hlam]
                              · linarith only [h1528, h2, hlam]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              rcases p1526_3 (m.d 0 4) (by simp) with h1537 | h1537
                              · rcases p1526_3 (m.d 1 4) (by simp) with h1538 | h1538
                                · linarith only [h1538, h2, hlam]
                                · linarith only [h11, h1538, hlam]
                              · linarith only [h1537, h5, hlam]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h498, h918, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p1526_1]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              rcases p1526_3 (m.d 0 4) (by simp) with h1543 | h1543
                              · rcases p1526_3 (m.d 1 4) (by simp) with h1544 | h1544
                                · linarith only [h1544, h2, hlam]
                                · rcases p1526_3 (m.d 2 4) (by simp) with h1546 | h1546
                                  · linarith only [h1546, h5, hlam]
                                  · rcases p1526_3 (m.d 3 4) (by simp) with h1548 | h1548
                                    · linarith only [h1548, h7, hlam]
                                    · linarith only [h1548, h918, hlam]
                              · linarith only [h1543, hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h2, hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h498, h912, h918, hc23, hc34, hlam, hphi, p1526_1]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h13, hlam, p1526_1]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h498, hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h5, hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h11, hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h912, hlam, p1526_1]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h916, hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h7, hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              rcases p1526_3 (m.d 0 4) (by simp) with h1563 | h1563
                              · rcases p1526_3 (m.d 1 4) (by simp) with h1564 | h1564
                                · linarith only [h13, h1564, hlam]
                                · rcases p1526_3 (m.d 2 4) (by simp) with h1566 | h1566
                                  · linarith only [h1566, h912, hlam]
                                  · rcases p1526_3 (m.d 3 4) (by simp) with h1568 | h1568
                                    · rcases p1526_3 (m.d 4 5) (by simp) with h1569 | h1569
                                      · linarith only [h1569, h918, hlam]
                                      · linarith only [h1569, h498, hlam]
                                    · linarith only [h13, h1568, hlam]
                              · linarith only [h1563, h2, hlam]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              rcases p1526_3 (m.d 0 4) (by simp) with h1574 | h1574
                              · rcases p1526_3 (m.d 1 4) (by simp) with h1575 | h1575
                                · linarith only [h13, h1575, hlam]
                                · linarith only [h11, h1575, hlam]
                              · linarith only [h1574, h5, hlam]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h0, h4, h498, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1526_1]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h9, hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h0, h11, h4, h7, h912, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1526_1]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h0, h4, h7, h912, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1526_1]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [h918, hlam, p1526_0]
                            · have p1526_0 := h1526c.1
                              have p1526_1 := h1526c.2.1
                              have p1526_2 := h1526c.2.2.1
                              have p1526_3 := h1526c.2.2.2
                              linarith only [hlam, p1526_0]
                    · linarith only [h1519, hlam, p1486_0]
                  · linarith only [h1518, h6, hlam]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h4, hlam, p1486_0]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h10, hlam, p1486_0]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [hlam, p1486_0]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h912, hlam, p1486_1]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h914, hlam, p1486_1]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h5, hlam, p1486_0]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h11, hlam, p1486_0]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1486_1]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [hlam, p1486_0]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h916, hlam, p1486_0]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h6, hlam, p1486_0]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h12, hlam, p1486_0]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1486_1, p919_1]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [h0, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1486_1, p919_1]
                · have p1486_0 := h1486c.1
                  have p1486_1 := h1486c.2.1
                  have p1486_2 := h1486c.2.2.1
                  have p1486_3 := h1486c.2.2.2
                  linarith only [hlam, p1486_0]
              · rcases h2bigk with h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [hlam, p1603_0]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p1603_1, p919_1]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h11, h4, h498, h7, h912, h918, hlam, p1603_2]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h11, h4, h498, h7, h918, hlam, p1603_2]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  rcases p1603_3 (m.d 0 2) (by simp) with h1608 | h1608
                  · rcases p1603_3 (m.d 1 2) (by simp) with h1609 | h1609
                    · linarith only [h0, h1609, hlam]
                    · linarith only [h12, h1609, hlam]
                  · linarith only [h1608, hlam, p1603_0]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h0, hlam, p1603_1]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [hlam, p1603_0]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  rcases p1603_3 (m.d 0 2) (by simp) with h1615 | h1615
                  · rcases p1603_3 (m.d 1 2) (by simp) with h1616 | h1616
                    · rcases p1603_3 (m.d 2 3) (by simp) with h1617 | h1617
                      · linarith only [h1617, hlam, p1603_0]
                      · rcases p1603_3 (m.d 2 4) (by simp) with h1619 | h1619
                        · linarith only [h11, h1619, hlam]
                        · linarith only [h1619, h912, hlam]
                    · linarith only [h1616, hlam, p1603_0]
                  · linarith only [h1615, h4, hlam]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  rcases p1603_3 (m.d 0 2) (by simp) with h1624 | h1624
                  · rcases p1603_3 (m.d 1 2) (by simp) with h1625 | h1625
                    · rcases p1603_3 (m.d 2 3) (by simp) with h1626 | h1626
                      · linarith only [h10, h1626, hlam]
                      · rcases p1603_3 (m.d 2 4) (by simp) with h1628 | h1628
                        · linarith only [h1628, hlam, p1603_0]
                        · rcases p1603_3 (m.d 2 5) (by simp) with h1630 | h1630
                          · linarith only [h12, h1630, hlam]
                          · linarith only [h1630, h916, hlam]
                    · linarith only [h1625, hlam, p1603_0]
                  · linarith only [h1624, h5, hlam]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  rcases p1603_3 (m.d 0 2) (by simp) with h1635 | h1635
                  · rcases p1603_3 (m.d 1 2) (by simp) with h1636 | h1636
                    · rcases p1603_3 (m.d 2 3) (by simp) with h1637 | h1637
                      · linarith only [h10, h1637, hlam]
                      · rcases p1603_3 (m.d 2 4) (by simp) with h1639 | h1639
                        · linarith only [h11, h1639, hlam]
                        · rcases p1603_3 (m.d 2 5) (by simp) with h1641 | h1641
                          · linarith only [h1641, hlam, p1603_0]
                          · rcases h4bigk with h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              rcases p1643_3 (m.d 0 4) (by simp) with h1645 | h1645
                              · rcases p1643_3 (m.d 1 4) (by simp) with h1646 | h1646
                                · linarith only [h1646, h2, hlam]
                                · rcases p1643_3 (m.d 2 4) (by simp) with h1648 | h1648
                                  · linarith only [h1648, h5, hlam]
                                  · rcases p1643_3 (m.d 3 4) (by simp) with h1650 | h1650
                                    · linarith only [h1650, h7, hlam]
                                    · linarith only [h13, h1650, hlam]
                              · linarith only [h1645, h2, hlam]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              rcases p1643_3 (m.d 0 4) (by simp) with h1654 | h1654
                              · rcases p1643_3 (m.d 1 4) (by simp) with h1655 | h1655
                                · linarith only [h1655, h2, hlam]
                                · linarith only [h11, h1655, hlam]
                              · linarith only [h1654, h5, hlam]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h498, h918, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p1643_1]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              rcases p1643_3 (m.d 0 4) (by simp) with h1660 | h1660
                              · rcases p1643_3 (m.d 1 4) (by simp) with h1661 | h1661
                                · linarith only [h1661, h2, hlam]
                                · rcases p1643_3 (m.d 2 4) (by simp) with h1663 | h1663
                                  · linarith only [h1663, h5, hlam]
                                  · rcases p1643_3 (m.d 3 4) (by simp) with h1665 | h1665
                                    · linarith only [h1665, h7, hlam]
                                    · linarith only [h1665, h918, hlam]
                              · linarith only [h1660, hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h2, hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h498, h912, h918, hc23, hc34, hlam, hphi, p1643_1]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h13, hlam, p1643_1]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h498, hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h5, hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h11, hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h912, hlam, p1643_1]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h916, hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h7, hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              rcases p1643_3 (m.d 0 4) (by simp) with h1680 | h1680
                              · rcases p1643_3 (m.d 1 4) (by simp) with h1681 | h1681
                                · linarith only [h13, h1681, hlam]
                                · rcases p1643_3 (m.d 2 4) (by simp) with h1683 | h1683
                                  · linarith only [h1683, h912, hlam]
                                  · rcases p1643_3 (m.d 3 4) (by simp) with h1685 | h1685
                                    · rcases p1643_3 (m.d 4 5) (by simp) with h1686 | h1686
                                      · linarith only [h1686, h918, hlam]
                                      · linarith only [h1686, h498, hlam]
                                    · linarith only [h13, h1685, hlam]
                              · linarith only [h1680, h2, hlam]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              rcases p1643_3 (m.d 0 4) (by simp) with h1691 | h1691
                              · rcases p1643_3 (m.d 1 4) (by simp) with h1692 | h1692
                                · linarith only [h13, h1692, hlam]
                                · linarith only [h11, h1692, hlam]
                              · linarith only [h1691, h5, hlam]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h0, h4, h498, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1643_1]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h9, hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h0, h11, h4, h7, h912, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1643_1]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h0, h4, h7, h912, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1643_1]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [h918, hlam, p1643_0]
                            · have p1643_0 := h1643c.1
                              have p1643_1 := h1643c.2.1
                              have p1643_2 := h1643c.2.2.1
                              have p1643_3 := h1643c.2.2.2
                              linarith only [hlam, p1643_0]
                    · linarith only [h1636, hlam, p1603_0]
                  · linarith only [h1635, h6, hlam]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h4, hlam, p1603_0]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h10, hlam, p1603_0]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [hlam, p1603_0]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h912, hlam, p1603_1]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h914, hlam, p1603_1]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h5, hlam, p1603_0]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h11, hlam, p1603_0]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1603_1]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [hlam, p1603_0]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h916, hlam, p1603_0]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h6, hlam, p1603_0]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h12, hlam, p1603_0]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1603_1, p919_1]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [h0, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1603_1, p919_1]
                · have p1603_0 := h1603c.1
                  have p1603_1 := h1603c.2.1
                  have p1603_2 := h1603c.2.2.1
                  have p1603_3 := h1603c.2.2.2
                  linarith only [hlam, p1603_0]
      · linarith only [h12, h1359, hlam]
    · linarith only [h1358, h3, hlam]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h1, hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h10, hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h13, hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h437, hlam, p919_1]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h2, hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h11, hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h0, h10, h4, h498, h7, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p919_1]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h498, hlam, p919_1]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h3, hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h12, hlam, p919_0]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h0, h10, h4, h498, h7, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p919_1]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [h0, h4, h498, h7, h918, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p919_1]
  · have p919_0 := h919c.1
    have p919_1 := h919c.2.1
    have p919_2 := h919c.2.2.1
    have p919_3 := h919c.2.2.2
    linarith only [hlam, p919_0]

end R2N4
