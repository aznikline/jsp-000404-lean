import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 0 4 5 (by decide) (by decide) with h6901 | h6901
  · rcases m.htr 1 2 3 (by decide) (by decide) with h6902 | h6902
    · rcases m.htr 1 2 4 (by decide) (by decide) with h6903 | h6903
      · rcases m.htr 1 2 5 (by decide) (by decide) with h6904 | h6904
        · rcases m.htr 1 3 4 (by decide) (by decide) with h6905 | h6905
          · linarith only [h0, h6310, h6316, h6900, h6905, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h6907 | h6907
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6908 | h6908
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6909 | h6909
                · linarith only [h6310, h6316, h6902, h6909, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6911 | h6911
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6912 | h6912
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6913 | h6913
                      · rcases h0bigk with h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c | h6914c
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [hlam, p6914_0]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h0, hlam, p6914_1]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h0, h6310, h6902, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6914_1]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h0, h6310, h6316, h6902, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6914_1]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          rcases p6914_3 (m.d 0 1) (by simp) with h6919 | h6919
                          · rcases p6914_3 (m.d 0 2) (by simp) with h6920 | h6920
                            · rcases p6914_3 (m.d 0 3) (by simp) with h6921 | h6921
                              · linarith only [h6310, h6921, hlam]
                              · linarith only [h6900, h6921, hlam]
                            · linarith only [h6315, h6920, hlam]
                          · linarith only [h6312, h6919, hlam]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6310, h6902, h6911, h6913, hc45, hlam, hphi, ht0b, ht5b, p6914_1, u0elo1]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [hlam, p6914_0]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6310, h6902, h6911, h6913, hc45, hlam, hphi, ht0b, ht5b, p6914_1, u0elo1]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6310, h6316, h6902, h6911, h6913, hc45, hlam, hphi, ht0b, ht5b, p6914_1, u0elo1]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          rcases p6914_3 (m.d 0 1) (by simp) with h6930 | h6930
                          · linarith only [h0, h6930, hlam]
                          · linarith only [h6312, h6930, hlam]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6310, hlam, p6914_1]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6313, hlam, p6914_1]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [hlam, p6914_0]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6316, hlam, p6914_1]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          rcases p6914_3 (m.d 0 1) (by simp) with h6937 | h6937
                          · rcases p6914_3 (m.d 0 2) (by simp) with h6938 | h6938
                            · rcases p6914_3 (m.d 0 3) (by simp) with h6939 | h6939
                              · rcases p6914_3 (m.d 0 4) (by simp) with h6940 | h6940
                                · rcases p6914_3 (m.d 0 5) (by simp) with h6941 | h6941
                                  · linarith only [h6900, h6941, hlam]
                                  · rcases h0emin with h6943 | h6943 | h6943 | h6943 | h6943
                                    · rcases h1bigk with h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c | h6944c
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [hlam, p6944_0]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h0, hlam, p6944_0]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h0, h6902, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6944_1]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h0, h6902, h6905, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6944_1]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        rcases p6944_3 (m.d 0 1) (by simp) with h6949 | h6949
                                        · rcases p6944_3 (m.d 1 2) (by simp) with h6950 | h6950
                                          · rcases p6944_3 (m.d 1 3) (by simp) with h6951 | h6951
                                            · linarith only [h6310, h6951, hlam]
                                            · linarith only [h6907, h6951, hlam]
                                          · linarith only [h6904, h6950, hlam]
                                        · linarith only [h6949, hlam, p6944_0]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h6943, hc12, hlam, ht01, p6944_1]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [hlam, p6944_0]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        rcases p6944_3 (m.d 0 1) (by simp) with h6958 | h6958
                                        · linarith only [h0, h6958, hlam]
                                        · linarith only [h6310, h6958, hlam]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        rcases p6944_3 (m.d 0 1) (by simp) with h6961 | h6961
                                        · linarith only [h0, h6961, hlam]
                                        · linarith only [h6311, h6961, hlam]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h0, h6311, h6312, h6316, hlam, p6914_1, p6944_2]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h6310, hlam, p6944_0]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h6902, hlam, p6944_1]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [hlam, p6944_0]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h6905, hlam, p6944_1]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h6310, h6904, h6911, h6913, hc45, hlam, hphi, ht0b, ht5b, p6944_1, u0elo0]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h6311, hlam, p6944_0]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h6903, hlam, p6944_1]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h0, h6311, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6944_1]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [hlam, p6944_0]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h0, h6311, h6904, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6944_1]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h6312, hlam, p6944_0]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h6904, hlam, p6944_1]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h6907, hlam, p6944_0]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [h6908, hlam, p6944_0]
                                      · have p6944_0 := h6944c.1
                                        have p6944_1 := h6944c.2.1
                                        have p6944_2 := h6944c.2.2.1
                                        have p6944_3 := h6944c.2.2.2
                                        linarith only [hlam, p6944_0]
                                    · rcases h1bigk with h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c | h6980c
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [hlam, p6980_0]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h0, hlam, p6980_0]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h0, h6902, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6980_1]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h0, h6902, h6905, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6980_1]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        rcases p6980_3 (m.d 0 1) (by simp) with h6985 | h6985
                                        · rcases p6980_3 (m.d 1 2) (by simp) with h6986 | h6986
                                          · rcases p6980_3 (m.d 1 3) (by simp) with h6987 | h6987
                                            · linarith only [h6310, h6987, hlam]
                                            · linarith only [h6907, h6987, hlam]
                                          · linarith only [h6904, h6986, hlam]
                                        · linarith only [h6985, hlam, p6980_0]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h6310, h6902, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6980_1]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [hlam, p6980_0]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        rcases p6980_3 (m.d 0 1) (by simp) with h6994 | h6994
                                        · linarith only [h0, h6994, hlam]
                                        · linarith only [h6310, h6994, hlam]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        rcases p6980_3 (m.d 0 1) (by simp) with h6997 | h6997
                                        · linarith only [h0, h6997, hlam]
                                        · linarith only [h6311, h6997, hlam]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h0, h6311, h6312, h6316, hlam, p6914_1, p6980_2]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h6310, hlam, p6980_0]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h6902, hlam, p6980_1]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [hlam, p6980_0]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h6905, hlam, p6980_1]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h6310, h6904, h6911, h6913, hc45, hlam, hphi, ht0b, ht5b, p6980_1, u0elo0]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h6311, hlam, p6980_0]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h6903, hlam, p6980_1]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h0, h6311, h6312, h6316, h6904, h6911, h6913, hc12, hc13, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p6914_1, p6980_1]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [hlam, p6980_0]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h0, h6311, h6904, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6980_1]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h6312, hlam, p6980_0]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h6904, hlam, p6980_1]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h6907, hlam, p6980_0]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [h6908, hlam, p6980_0]
                                      · have p6980_0 := h6980c.1
                                        have p6980_1 := h6980c.2.1
                                        have p6980_2 := h6980c.2.2.1
                                        have p6980_3 := h6980c.2.2.2
                                        linarith only [hlam, p6980_0]
                                    · rcases h1bigk with h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c | h7016c
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [hlam, p7016_0]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h0, hlam, p7016_0]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h0, h6902, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7016_1]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h0, h6902, h6905, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7016_1]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        rcases p7016_3 (m.d 0 1) (by simp) with h7021 | h7021
                                        · rcases p7016_3 (m.d 1 2) (by simp) with h7022 | h7022
                                          · rcases p7016_3 (m.d 1 3) (by simp) with h7023 | h7023
                                            · linarith only [h6310, h7023, hlam]
                                            · linarith only [h6907, h7023, hlam]
                                          · linarith only [h6904, h7022, hlam]
                                        · linarith only [h7021, hlam, p7016_0]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h6310, h6902, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7016_1]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [hlam, p7016_0]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        rcases p7016_3 (m.d 0 1) (by simp) with h7030 | h7030
                                        · linarith only [h0, h7030, hlam]
                                        · linarith only [h6310, h7030, hlam]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        rcases p7016_3 (m.d 0 1) (by simp) with h7033 | h7033
                                        · linarith only [h0, h7033, hlam]
                                        · linarith only [h6311, h7033, hlam]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h0, h6311, h6312, h6316, hlam, p6914_1, p7016_2]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h6310, hlam, p7016_0]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h6902, hlam, p7016_1]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [hlam, p7016_0]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h6905, hlam, p7016_1]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h6310, h6904, h6911, h6913, hc45, hlam, hphi, ht0b, ht5b, p7016_1, u0elo0]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h6311, hlam, p7016_0]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h6903, hlam, p7016_1]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h0, h6311, h6312, h6316, h6904, h6911, h6913, hc12, hc13, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p6914_1, p7016_1]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [hlam, p7016_0]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h0, h6311, h6904, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7016_1]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h6312, hlam, p7016_0]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h6904, hlam, p7016_1]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h6907, hlam, p7016_0]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [h6908, hlam, p7016_0]
                                      · have p7016_0 := h7016c.1
                                        have p7016_1 := h7016c.2.1
                                        have p7016_2 := h7016c.2.2.1
                                        have p7016_3 := h7016c.2.2.2
                                        linarith only [hlam, p7016_0]
                                    · rcases h1bigk with h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c | h7052c
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [hlam, p7052_0]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h0, hlam, p7052_0]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h0, h6902, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7052_1]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h0, h6902, h6905, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7052_1]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        rcases p7052_3 (m.d 0 1) (by simp) with h7057 | h7057
                                        · rcases p7052_3 (m.d 1 2) (by simp) with h7058 | h7058
                                          · rcases p7052_3 (m.d 1 3) (by simp) with h7059 | h7059
                                            · linarith only [h6310, h7059, hlam]
                                            · linarith only [h6907, h7059, hlam]
                                          · linarith only [h6904, h7058, hlam]
                                        · linarith only [h7057, hlam, p7052_0]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h6310, h6902, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7052_1]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [hlam, p7052_0]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        rcases p7052_3 (m.d 0 1) (by simp) with h7066 | h7066
                                        · linarith only [h0, h7066, hlam]
                                        · linarith only [h6310, h7066, hlam]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        rcases p7052_3 (m.d 0 1) (by simp) with h7069 | h7069
                                        · linarith only [h0, h7069, hlam]
                                        · linarith only [h6311, h7069, hlam]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h0, h6311, h6312, h6316, hlam, p6914_1, p7052_2]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h6310, hlam, p7052_0]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h6902, hlam, p7052_1]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [hlam, p7052_0]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h6905, hlam, p7052_1]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h6310, h6904, h6911, h6913, hc45, hlam, hphi, ht0b, ht5b, p7052_1, u0elo0]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h6311, hlam, p7052_0]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h6903, hlam, p7052_1]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h0, h6311, h6312, h6316, h6904, h6911, h6913, hc12, hc13, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p6914_1, p7052_1]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [hlam, p7052_0]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h0, h6311, h6904, h6911, h6913, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7052_1]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h6312, hlam, p7052_0]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h6904, hlam, p7052_1]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h6907, hlam, p7052_0]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [h6908, hlam, p7052_0]
                                      · have p7052_0 := h7052c.1
                                        have p7052_1 := h7052c.2.1
                                        have p7052_2 := h7052c.2.2.1
                                        have p7052_3 := h7052c.2.2.2
                                        linarith only [hlam, p7052_0]
                                    · linarith only [h6316, h6943, hc34, hlam, ht01, ht12, ht23, p6914_1]
                                · linarith only [h6901, h6940, hlam]
                              · linarith only [h6900, h6939, hlam]
                            · linarith only [h6315, h6938, hlam]
                          · linarith only [h6312, h6937, hlam]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6311, hlam, p6914_0]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6314, hlam, p6914_0]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6310, h6902, h6911, h6913, hc45, hlam, hphi, ht0b, ht5b, p6914_1, u0elo3]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [hlam, p6914_0]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          rcases p6914_3 (m.d 0 1) (by simp) with h7097 | h7097
                          · rcases p6914_3 (m.d 0 2) (by simp) with h7098 | h7098
                            · rcases p6914_3 (m.d 0 3) (by simp) with h7099 | h7099
                              · linarith only [h6316, h7099, hlam]
                              · linarith only [h6900, h7099, hlam]
                            · linarith only [h6315, h7098, hlam]
                          · linarith only [h6312, h7097, hlam]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6312, hlam, p6914_0]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6315, hlam, p6914_1]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6900, hlam, p6914_0]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [h6901, hlam, p6914_1]
                        · have p6914_0 := h6914c.1
                          have p6914_1 := h6914c.2.1
                          have p6914_2 := h6914c.2.2.1
                          have p6914_3 := h6914c.2.2.2
                          linarith only [hlam, p6914_0]
                      · linarith only [h6316, h6901, h6913, hlam]
                    · linarith only [h0, h6311, h6908, h6912, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h6316, h6900, h6911, hc23, hc34, hlam, hphi]
              · linarith only [h0, h6311, h6901, h6905, h6907, h6908, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h6316, h6900, h6907, hc13, hc34, hlam, hphi]
        · linarith only [h0, h6315, h6904, hlam]
      · linarith only [h0, h6314, h6903, hlam]
    · linarith only [h0, h6313, h6902, hlam]
  · linarith only [h6316, h6900, h6901, hlam]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7119 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7120 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7121 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h7122 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h6310, h6316, h7122, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7119 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7120 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7121 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h7122 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h7124 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h6310, h6900, h7124, hlam]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x0_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7119 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7120 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7121 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h7122 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h7124 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h7126 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 2 3 4 (by decide) (by decide) with h7127 | h7127
  · linarith only [h6311, h6313, h6316, h7126, h7127, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h7129 | h7129
    · linarith only [h6310, h6900, h7119, h7129, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h7131 | h7131
      · rcases m.htr 3 4 5 (by decide) (by decide) with h7132 | h7132
        · rcases h0bigk with h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c | h7133c
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [hlam, p7133_0]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h0, hlam, p7133_1]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            rcases p7133_3 (m.d 0 1) (by simp) with h7136 | h7136
            · rcases p7133_3 (m.d 0 2) (by simp) with h7137 | h7137
              · rcases p7133_3 (m.d 0 3) (by simp) with h7138 | h7138
                · linarith only [h6310, h7138, hlam]
                · rcases p7133_3 (m.d 0 4) (by simp) with h7140 | h7140
                  · linarith only [h6311, h7140, hlam]
                  · linarith only [h6316, h7140, hlam]
              · linarith only [h6313, h7137, hlam]
            · linarith only [h6310, h7136, hlam]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h0, h6311, h7120, h7131, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7133_1]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            rcases p7133_3 (m.d 0 1) (by simp) with h7146 | h7146
            · rcases p7133_3 (m.d 0 2) (by simp) with h7147 | h7147
              · rcases p7133_3 (m.d 0 3) (by simp) with h7148 | h7148
                · linarith only [h6310, h7148, hlam]
                · rcases p7133_3 (m.d 0 4) (by simp) with h7150 | h7150
                  · linarith only [h6311, h7150, hlam]
                  · linarith only [h7118, h7150, hlam]
              · linarith only [h6315, h7147, hlam]
            · linarith only [h6312, h7146, hlam]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h6310, h7119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7133_1, u0elo1]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [hlam, p7133_0]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            rcases p7133_3 (m.d 0 1) (by simp) with h7157 | h7157
            · linarith only [h0, h7157, hlam]
            · linarith only [h6310, h7157, hlam]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h6311, h7120, h7131, hc45, hlam, hphi, ht0b, ht5b, p7133_1, u0elo1]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            rcases p7133_3 (m.d 0 1) (by simp) with h7161 | h7161
            · linarith only [h0, h7161, hlam]
            · linarith only [h6312, h7161, hlam]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h6310, hlam, p7133_1]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h6313, hlam, p7133_1]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [hlam, p7133_0]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h6316, hlam, p7133_1]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h6900, hlam, p7133_1]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h6311, hlam, p7133_0]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h6314, hlam, p7133_0]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            rcases p7133_3 (m.d 0 1) (by simp) with h7171 | h7171
            · rcases p7133_3 (m.d 0 2) (by simp) with h7172 | h7172
              · rcases p7133_3 (m.d 0 3) (by simp) with h7173 | h7173
                · linarith only [h6316, h7173, hlam]
                · rcases p7133_3 (m.d 0 4) (by simp) with h7175 | h7175
                  · rcases p7133_3 (m.d 0 5) (by simp) with h7176 | h7176
                    · linarith only [h7118, h7176, hlam]
                    · linarith only [h6900, h7176, hlam]
                  · linarith only [h6316, h7175, hlam]
              · linarith only [h6313, h7172, hlam]
            · linarith only [h6310, h7171, hlam]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [hlam, p7133_0]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            rcases p7133_3 (m.d 0 1) (by simp) with h7183 | h7183
            · rcases p7133_3 (m.d 0 2) (by simp) with h7184 | h7184
              · rcases p7133_3 (m.d 0 3) (by simp) with h7185 | h7185
                · linarith only [h6316, h7185, hlam]
                · rcases p7133_3 (m.d 0 4) (by simp) with h7187 | h7187
                  · rcases p7133_3 (m.d 0 5) (by simp) with h7188 | h7188
                    · linarith only [h7118, h7188, hlam]
                    · rcases h0emin with h7190 | h7190 | h7190 | h7190 | h7190
                      · rcases h1bigk with h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [hlam, p7191_0]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h0, hlam, p7191_0]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          rcases p7191_3 (m.d 0 1) (by simp) with h7194 | h7194
                          · rcases p7191_3 (m.d 1 2) (by simp) with h7195 | h7195
                            · rcases p7191_3 (m.d 1 3) (by simp) with h7196 | h7196
                              · linarith only [h7196, hlam, p7191_0]
                              · rcases p7191_3 (m.d 1 4) (by simp) with h7198 | h7198
                                · linarith only [h6311, h7198, hlam]
                                · linarith only [h7122, h7198, hlam]
                            · linarith only [h7119, h7195, hlam]
                          · linarith only [h7194, hlam, p7191_0]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h0, h7120, h7131, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7191_1]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          rcases p7191_3 (m.d 0 1) (by simp) with h7204 | h7204
                          · rcases p7191_3 (m.d 1 2) (by simp) with h7205 | h7205
                            · rcases p7191_3 (m.d 1 3) (by simp) with h7206 | h7206
                              · linarith only [h6310, h7206, hlam]
                              · rcases p7191_3 (m.d 1 4) (by simp) with h7208 | h7208
                                · linarith only [h6311, h7208, hlam]
                                · linarith only [h7126, h7208, hlam]
                            · linarith only [h7121, h7205, hlam]
                          · linarith only [h7204, hlam, p7191_0]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h7190, hc12, hlam, ht01, p7191_1]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [hlam, p7191_0]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h0, h6310, h6311, h6900, hlam, p7133_1, p7191_2]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          rcases p7191_3 (m.d 0 1) (by simp) with h7216 | h7216
                          · linarith only [h0, h7216, hlam]
                          · linarith only [h6311, h7216, hlam]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h0, h6311, h6312, hlam, p7133_1, p7191_2]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h6310, hlam, p7191_0]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h7119, hlam, p7191_1]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [hlam, p7191_0]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h7122, hlam, p7191_1]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h7124, hlam, p7191_1]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h6311, hlam, p7191_0]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h7120, hlam, p7191_1]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h6311, h7119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7191_1, u0elo0]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [hlam, p7191_0]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h0, h6311, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7191_1]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h6312, hlam, p7191_0]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h7121, hlam, p7191_1]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h0, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7191_1]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [h7126, hlam, p7191_0]
                        · have p7191_0 := h7191c.1
                          have p7191_1 := h7191c.2.1
                          have p7191_2 := h7191c.2.2.1
                          have p7191_3 := h7191c.2.2.2
                          linarith only [hlam, p7191_0]
                      · rcases h1bigk with h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [hlam, p7235_0]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h0, hlam, p7235_0]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          rcases p7235_3 (m.d 0 1) (by simp) with h7238 | h7238
                          · rcases p7235_3 (m.d 1 2) (by simp) with h7239 | h7239
                            · rcases p7235_3 (m.d 1 3) (by simp) with h7240 | h7240
                              · linarith only [h7240, hlam, p7235_0]
                              · rcases p7235_3 (m.d 1 4) (by simp) with h7242 | h7242
                                · linarith only [h6311, h7242, hlam]
                                · linarith only [h7122, h7242, hlam]
                            · linarith only [h7119, h7239, hlam]
                          · linarith only [h7238, hlam, p7235_0]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h0, h7120, h7131, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7235_1]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          rcases p7235_3 (m.d 0 1) (by simp) with h7248 | h7248
                          · rcases p7235_3 (m.d 1 2) (by simp) with h7249 | h7249
                            · rcases p7235_3 (m.d 1 3) (by simp) with h7250 | h7250
                              · linarith only [h6310, h7250, hlam]
                              · rcases p7235_3 (m.d 1 4) (by simp) with h7252 | h7252
                                · linarith only [h6311, h7252, hlam]
                                · linarith only [h7126, h7252, hlam]
                            · linarith only [h7121, h7249, hlam]
                          · linarith only [h7248, hlam, p7235_0]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h6311, h7120, h7131, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7235_1]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [hlam, p7235_0]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h0, h6310, h6311, h6900, hlam, p7133_1, p7235_2]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          rcases p7235_3 (m.d 0 1) (by simp) with h7260 | h7260
                          · linarith only [h0, h7260, hlam]
                          · linarith only [h6311, h7260, hlam]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h0, h6311, h6312, hlam, p7133_1, p7235_2]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h6310, hlam, p7235_0]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h7119, hlam, p7235_1]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [hlam, p7235_0]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h7122, hlam, p7235_1]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h7124, hlam, p7235_1]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h6311, hlam, p7235_0]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h7120, hlam, p7235_1]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h6311, h7119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7235_1, u0elo0]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [hlam, p7235_0]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h0, h6311, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7235_1]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h6312, hlam, p7235_0]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h7121, hlam, p7235_1]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h0, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7235_1]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [h7126, hlam, p7235_0]
                        · have p7235_0 := h7235c.1
                          have p7235_1 := h7235c.2.1
                          have p7235_2 := h7235c.2.2.1
                          have p7235_3 := h7235c.2.2.2
                          linarith only [hlam, p7235_0]
                      · linarith only [h6900, h7190, hlam, p7133_1, u0elo3]
                      · rcases h1bigk with h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c | h7280c
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [hlam, p7280_0]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h0, hlam, p7280_0]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          rcases p7280_3 (m.d 0 1) (by simp) with h7283 | h7283
                          · rcases p7280_3 (m.d 1 2) (by simp) with h7284 | h7284
                            · rcases p7280_3 (m.d 1 3) (by simp) with h7285 | h7285
                              · linarith only [h7285, hlam, p7280_0]
                              · rcases p7280_3 (m.d 1 4) (by simp) with h7287 | h7287
                                · linarith only [h6311, h7287, hlam]
                                · linarith only [h7122, h7287, hlam]
                            · linarith only [h7119, h7284, hlam]
                          · linarith only [h7283, hlam, p7280_0]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h0, h7120, h7131, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7280_1]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          rcases p7280_3 (m.d 0 1) (by simp) with h7293 | h7293
                          · rcases p7280_3 (m.d 1 2) (by simp) with h7294 | h7294
                            · rcases p7280_3 (m.d 1 3) (by simp) with h7295 | h7295
                              · linarith only [h6310, h7295, hlam]
                              · rcases p7280_3 (m.d 1 4) (by simp) with h7297 | h7297
                                · linarith only [h6311, h7297, hlam]
                                · linarith only [h7126, h7297, hlam]
                            · linarith only [h7121, h7294, hlam]
                          · linarith only [h7293, hlam, p7280_0]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h6310, h6311, h6900, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7133_1, p7280_1]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [hlam, p7280_0]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h0, h6310, h6311, h6900, hlam, p7133_1, p7280_2]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          rcases p7280_3 (m.d 0 1) (by simp) with h7305 | h7305
                          · linarith only [h0, h7305, hlam]
                          · linarith only [h6311, h7305, hlam]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h0, h6311, h6312, hlam, p7133_1, p7280_2]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h6310, hlam, p7280_0]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h7119, hlam, p7280_1]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [hlam, p7280_0]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h7122, hlam, p7280_1]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h7124, hlam, p7280_1]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h6311, hlam, p7280_0]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h7120, hlam, p7280_1]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h6311, h7119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7280_1, u0elo0]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [hlam, p7280_0]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h0, h6311, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7280_1]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h6312, hlam, p7280_0]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h7121, hlam, p7280_1]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h0, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7280_1]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [h7126, hlam, p7280_0]
                        · have p7280_0 := h7280c.1
                          have p7280_1 := h7280c.2.1
                          have p7280_2 := h7280c.2.2.1
                          have p7280_3 := h7280c.2.2.2
                          linarith only [hlam, p7280_0]
                      · linarith only [h7190, hlam, p7133_1, u0elo3]
                  · linarith only [h7118, h7187, hlam]
              · linarith only [h6315, h7184, hlam]
            · linarith only [h6312, h7183, hlam]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h6312, hlam, p7133_0]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h6315, hlam, p7133_1]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            rcases p7133_3 (m.d 0 1) (by simp) with h7330 | h7330
            · rcases p7133_3 (m.d 0 2) (by simp) with h7331 | h7331
              · rcases p7133_3 (m.d 0 3) (by simp) with h7332 | h7332
                · linarith only [h6900, h7332, hlam]
                · rcases p7133_3 (m.d 0 4) (by simp) with h7334 | h7334
                  · rcases p7133_3 (m.d 0 5) (by simp) with h7335 | h7335
                    · rcases h0emin with h7336 | h7336 | h7336 | h7336 | h7336
                      · rcases h1bigk with h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [hlam, p7337_0]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h0, hlam, p7337_0]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          rcases p7337_3 (m.d 0 1) (by simp) with h7340 | h7340
                          · rcases p7337_3 (m.d 1 2) (by simp) with h7341 | h7341
                            · rcases p7337_3 (m.d 1 3) (by simp) with h7342 | h7342
                              · linarith only [h7342, hlam, p7337_0]
                              · rcases p7337_3 (m.d 1 4) (by simp) with h7344 | h7344
                                · linarith only [h6311, h7344, hlam]
                                · linarith only [h7122, h7344, hlam]
                            · linarith only [h7119, h7341, hlam]
                          · linarith only [h7340, hlam, p7337_0]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h0, h7120, h7131, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7337_1]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          rcases p7337_3 (m.d 0 1) (by simp) with h7350 | h7350
                          · rcases p7337_3 (m.d 1 2) (by simp) with h7351 | h7351
                            · rcases p7337_3 (m.d 1 3) (by simp) with h7352 | h7352
                              · linarith only [h6310, h7352, hlam]
                              · rcases p7337_3 (m.d 1 4) (by simp) with h7354 | h7354
                                · linarith only [h6311, h7354, hlam]
                                · linarith only [h7126, h7354, hlam]
                            · linarith only [h7121, h7351, hlam]
                          · linarith only [h7350, hlam, p7337_0]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h7336, hc12, hlam, ht01, p7337_1]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [hlam, p7337_0]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h0, h6310, h6311, h7118, hlam, p7133_1, p7337_2]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          rcases p7337_3 (m.d 0 1) (by simp) with h7362 | h7362
                          · linarith only [h0, h7362, hlam]
                          · linarith only [h6311, h7362, hlam]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          rcases p7337_3 (m.d 0 1) (by simp) with h7365 | h7365
                          · linarith only [h0, h7365, hlam]
                          · linarith only [h6312, h7365, hlam]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h6310, hlam, p7337_0]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h7119, hlam, p7337_1]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [hlam, p7337_0]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h7122, hlam, p7337_1]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h7124, hlam, p7337_1]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h6311, hlam, p7337_0]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h7120, hlam, p7337_1]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h6311, h7119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7337_1, u0elo0]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [hlam, p7337_0]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h0, h6311, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7337_1]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h6312, hlam, p7337_0]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h7121, hlam, p7337_1]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h0, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7337_1]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [h7126, hlam, p7337_0]
                        · have p7337_0 := h7337c.1
                          have p7337_1 := h7337c.2.1
                          have p7337_2 := h7337c.2.2.1
                          have p7337_3 := h7337c.2.2.2
                          linarith only [hlam, p7337_0]
                      · rcases h1bigk with h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c | h7383c
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [hlam, p7383_0]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h0, hlam, p7383_0]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          rcases p7383_3 (m.d 0 1) (by simp) with h7386 | h7386
                          · rcases p7383_3 (m.d 1 2) (by simp) with h7387 | h7387
                            · rcases p7383_3 (m.d 1 3) (by simp) with h7388 | h7388
                              · linarith only [h7388, hlam, p7383_0]
                              · rcases p7383_3 (m.d 1 4) (by simp) with h7390 | h7390
                                · linarith only [h6311, h7390, hlam]
                                · linarith only [h7122, h7390, hlam]
                            · linarith only [h7119, h7387, hlam]
                          · linarith only [h7386, hlam, p7383_0]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h0, h7120, h7131, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7383_1]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          rcases p7383_3 (m.d 0 1) (by simp) with h7396 | h7396
                          · rcases p7383_3 (m.d 1 2) (by simp) with h7397 | h7397
                            · rcases p7383_3 (m.d 1 3) (by simp) with h7398 | h7398
                              · linarith only [h6310, h7398, hlam]
                              · rcases p7383_3 (m.d 1 4) (by simp) with h7400 | h7400
                                · linarith only [h6311, h7400, hlam]
                                · linarith only [h7126, h7400, hlam]
                            · linarith only [h7121, h7397, hlam]
                          · linarith only [h7396, hlam, p7383_0]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h6311, h7120, h7131, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7383_1]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [hlam, p7383_0]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h0, h6310, h6311, h7118, hlam, p7133_1, p7383_2]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          rcases p7383_3 (m.d 0 1) (by simp) with h7408 | h7408
                          · linarith only [h0, h7408, hlam]
                          · linarith only [h6311, h7408, hlam]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          rcases p7383_3 (m.d 0 1) (by simp) with h7411 | h7411
                          · linarith only [h0, h7411, hlam]
                          · linarith only [h6312, h7411, hlam]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h6310, hlam, p7383_0]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h7119, hlam, p7383_1]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [hlam, p7383_0]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h7122, hlam, p7383_1]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h7124, hlam, p7383_1]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h6311, hlam, p7383_0]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h7120, hlam, p7383_1]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h6311, h7119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7383_1, u0elo0]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [hlam, p7383_0]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h0, h6311, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7383_1]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h6312, hlam, p7383_0]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h7121, hlam, p7383_1]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h0, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7383_1]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [h7126, hlam, p7383_0]
                        · have p7383_0 := h7383c.1
                          have p7383_1 := h7383c.2.1
                          have p7383_2 := h7383c.2.2.1
                          have p7383_3 := h7383c.2.2.2
                          linarith only [hlam, p7383_0]
                      · linarith only [h7118, h7336, hlam, p7133_1, u0elo3]
                      · rcases h1bigk with h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c | h7430c
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [hlam, p7430_0]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h0, hlam, p7430_0]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          rcases p7430_3 (m.d 0 1) (by simp) with h7433 | h7433
                          · rcases p7430_3 (m.d 1 2) (by simp) with h7434 | h7434
                            · rcases p7430_3 (m.d 1 3) (by simp) with h7435 | h7435
                              · linarith only [h7435, hlam, p7430_0]
                              · rcases p7430_3 (m.d 1 4) (by simp) with h7437 | h7437
                                · linarith only [h6311, h7437, hlam]
                                · linarith only [h7122, h7437, hlam]
                            · linarith only [h7119, h7434, hlam]
                          · linarith only [h7433, hlam, p7430_0]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h0, h7120, h7131, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7430_1]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          rcases p7430_3 (m.d 0 1) (by simp) with h7443 | h7443
                          · rcases p7430_3 (m.d 1 2) (by simp) with h7444 | h7444
                            · rcases p7430_3 (m.d 1 3) (by simp) with h7445 | h7445
                              · linarith only [h6310, h7445, hlam]
                              · rcases p7430_3 (m.d 1 4) (by simp) with h7447 | h7447
                                · linarith only [h6311, h7447, hlam]
                                · linarith only [h7126, h7447, hlam]
                            · linarith only [h7121, h7444, hlam]
                          · linarith only [h7443, hlam, p7430_0]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h6310, h6311, h7118, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7133_1, p7430_1]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [hlam, p7430_0]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h0, h6310, h6311, h7118, hlam, p7133_1, p7430_2]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          rcases p7430_3 (m.d 0 1) (by simp) with h7455 | h7455
                          · linarith only [h0, h7455, hlam]
                          · linarith only [h6311, h7455, hlam]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          rcases p7430_3 (m.d 0 1) (by simp) with h7458 | h7458
                          · linarith only [h0, h7458, hlam]
                          · linarith only [h6312, h7458, hlam]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h6310, hlam, p7430_0]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h7119, hlam, p7430_1]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [hlam, p7430_0]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h7122, hlam, p7430_1]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h7124, hlam, p7430_1]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h6311, hlam, p7430_0]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h7120, hlam, p7430_1]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h6311, h7119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7430_1, u0elo0]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [hlam, p7430_0]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h0, h6311, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7430_1]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h6312, hlam, p7430_0]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h7121, hlam, p7430_1]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h0, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7430_1]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [h7126, hlam, p7430_0]
                        · have p7430_0 := h7430c.1
                          have p7430_1 := h7430c.2.1
                          have p7430_2 := h7430c.2.2.1
                          have p7430_3 := h7430c.2.2.2
                          linarith only [hlam, p7430_0]
                      · rcases h1bigk with h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c | h7476c
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [hlam, p7476_0]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h0, hlam, p7476_0]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          rcases p7476_3 (m.d 0 1) (by simp) with h7479 | h7479
                          · rcases p7476_3 (m.d 1 2) (by simp) with h7480 | h7480
                            · rcases p7476_3 (m.d 1 3) (by simp) with h7481 | h7481
                              · linarith only [h7481, hlam, p7476_0]
                              · rcases p7476_3 (m.d 1 4) (by simp) with h7483 | h7483
                                · linarith only [h6311, h7483, hlam]
                                · linarith only [h7122, h7483, hlam]
                            · linarith only [h7119, h7480, hlam]
                          · linarith only [h7479, hlam, p7476_0]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h0, h7120, h7131, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7476_1]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          rcases p7476_3 (m.d 0 1) (by simp) with h7489 | h7489
                          · rcases p7476_3 (m.d 1 2) (by simp) with h7490 | h7490
                            · rcases p7476_3 (m.d 1 3) (by simp) with h7491 | h7491
                              · linarith only [h6310, h7491, hlam]
                              · rcases p7476_3 (m.d 1 4) (by simp) with h7493 | h7493
                                · linarith only [h6311, h7493, hlam]
                                · linarith only [h7126, h7493, hlam]
                            · linarith only [h7121, h7490, hlam]
                          · linarith only [h7489, hlam, p7476_0]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h6311, h7120, h7131, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7476_1]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [hlam, p7476_0]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h0, h6310, h6311, h7118, hlam, p7133_1, p7476_2]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          rcases p7476_3 (m.d 0 1) (by simp) with h7501 | h7501
                          · linarith only [h0, h7501, hlam]
                          · linarith only [h6311, h7501, hlam]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          rcases p7476_3 (m.d 0 1) (by simp) with h7504 | h7504
                          · linarith only [h0, h7504, hlam]
                          · linarith only [h6312, h7504, hlam]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h6310, hlam, p7476_0]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h7119, hlam, p7476_1]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [hlam, p7476_0]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h7122, hlam, p7476_1]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h7124, hlam, p7476_1]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h6311, hlam, p7476_0]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h7120, hlam, p7476_1]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h6311, h7119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7476_1, u0elo0]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [hlam, p7476_0]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h0, h6311, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7476_1]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h6312, hlam, p7476_0]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h7121, hlam, p7476_1]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h0, h6312, h7119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7476_1]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [h7126, hlam, p7476_0]
                        · have p7476_0 := h7476c.1
                          have p7476_1 := h7476c.2.1
                          have p7476_2 := h7476c.2.2.1
                          have p7476_3 := h7476c.2.2.2
                          linarith only [hlam, p7476_0]
                    · linarith only [h6900, h7335, hlam]
                  · linarith only [h6316, h7334, hlam]
              · linarith only [h6313, h7331, hlam]
            · linarith only [h6310, h7330, hlam]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [h7118, hlam, p7133_1]
          · have p7133_0 := h7133c.1
            have p7133_1 := h7133c.2.1
            have p7133_2 := h7133c.2.2.1
            have p7133_3 := h7133c.2.2.2
            linarith only [hlam, p7133_0]
        · linarith only [h6314, h6316, h7131, h7132, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
      · linarith only [h0, h6311, h7126, h7131, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]

end R2N4
