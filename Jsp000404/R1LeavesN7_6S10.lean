import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S8
import Jsp000404.R1LeavesN7_6S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13584000 in
set_option maxHeartbeats 13584000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h5410 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h5412 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h5414 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h5872 | h5872
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5873 | h5873
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5874 | h5874
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5875 | h5875
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5876 | h5876
          · linarith only [h0, h5412, h5876, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5878 | h5878
            · linarith only [h0, h5414, h5878, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5880 | h5880
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5881 | h5881
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5882 | h5882
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5883 | h5883
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5884 | h5884
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5885 | h5885
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5886 | h5886
                          · rcases h0bigk with h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [hlam, p5887_0]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h1, h5876, hc02, hc23, hlam, hphi, p5887_1]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h1, hlam, p5887_0]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h0, h1, h5414, h5876, hc12, hc23, hlam, hphi, p5887_1]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              rcases p5887_3 (m.d 0 1) (by simp) with h5892 | h5892
                              · rcases p5887_3 (m.d 0 2) (by simp) with h5893 | h5893
                                · linarith only [h0, h5893, hlam]
                                · linarith only [h5872, h5893, hlam]
                              · linarith only [h5411, h5892, hlam]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h0, hlam, p5887_0]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [hlam, p5887_0]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h5412, hlam, p5887_0]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h5414, hlam, p5887_1]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              rcases p5887_3 (m.d 0 1) (by simp) with h5901 | h5901
                              · rcases p5887_3 (m.d 0 2) (by simp) with h5902 | h5902
                                · rcases p5887_3 (m.d 0 3) (by simp) with h5903 | h5903
                                  · rcases p5887_3 (m.d 0 4) (by simp) with h5904 | h5904
                                    · rcases p5887_3 (m.d 0 5) (by simp) with h5905 | h5905
                                      · linarith only [h5872, h5905, hlam]
                                      · rcases h0emin with h5907 | h5907 | h5907 | h5907 | h5907
                                        · rcases h2bigk with h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5880, h5884, h5886, hc45, hlam, hphi, ht0b, ht5b, p5908_1, u0elo1]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5412, hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5414, hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            rcases p5908_3 (m.d 0 2) (by simp) with h5913 | h5913
                                            · rcases p5908_3 (m.d 1 2) (by simp) with h5914 | h5914
                                              · linarith only [h0, h5914, hlam]
                                              · linarith only [h5880, h5914, hlam]
                                            · linarith only [h5913, hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h0, hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5876, hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5878, hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h0, h1, h5876, h5884, h5886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5908_1]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5411, h5880, h5884, h5886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5887_1, p5908_1]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            rcases p5908_3 (m.d 0 2) (by simp) with h5924 | h5924
                                            · linarith only [h5412, h5924, hlam]
                                            · linarith only [h0, h5924, hlam]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5411, h5414, h5880, h5884, h5886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5887_1, p5908_1]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h0, h1, h5411, h5876, h5880, hlam, p5887_1, p5908_2]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p5887_1, p5908_1]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            rcases p5908_3 (m.d 0 2) (by simp) with h5931 | h5931
                                            · linarith only [h5414, h5931, hlam]
                                            · linarith only [h0, h5931, hlam]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5883, hlam, p5908_1]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5411, h5414, h5880, hlam, p5887_1, p5908_2]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5872, hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5880, hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5884, hlam, p5908_1]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [h5885, hlam, p5908_0]
                                          · have p5908_0 := h5908c.1
                                            have p5908_1 := h5908c.2.1
                                            have p5908_2 := h5908c.2.2.1
                                            have p5908_3 := h5908c.2.2.2
                                            linarith only [hlam, p5908_0]
                                        · rcases h2bigk with h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5414, hc12, hc24, hlam, hphi, p5942_1]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5412, hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5414, hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            rcases p5942_3 (m.d 0 2) (by simp) with h5947 | h5947
                                            · rcases p5942_3 (m.d 1 2) (by simp) with h5948 | h5948
                                              · linarith only [h0, h5948, hlam]
                                              · linarith only [h5880, h5948, hlam]
                                            · linarith only [h5947, hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h0, hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5876, hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5878, hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h0, h1, h5876, h5884, h5886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5942_1]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5411, h5880, h5884, h5886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5887_1, p5942_1]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            rcases p5942_3 (m.d 0 2) (by simp) with h5958 | h5958
                                            · linarith only [h5412, h5958, hlam]
                                            · linarith only [h0, h5958, hlam]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5411, h5414, h5880, h5884, h5886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5887_1, p5942_1]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h0, h1, h5411, h5876, h5880, hlam, p5887_1, p5942_2]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5411, h5880, h5884, h5886, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5887_1, p5942_1]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            rcases p5942_3 (m.d 0 2) (by simp) with h5965 | h5965
                                            · linarith only [h5414, h5965, hlam]
                                            · linarith only [h0, h5965, hlam]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5883, hlam, p5942_1]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5411, h5414, h5880, hlam, p5887_1, p5942_2]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5872, hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5880, hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5884, hlam, p5942_1]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [h5885, hlam, p5942_0]
                                          · have p5942_0 := h5942c.1
                                            have p5942_1 := h5942c.2.1
                                            have p5942_2 := h5942c.2.2.1
                                            have p5942_3 := h5942c.2.2.2
                                            linarith only [hlam, p5942_0]
                                        · rcases h2bigk with h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c | h5976c
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5414, hc12, hc24, hlam, hphi, p5976_1]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5412, hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5414, hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            rcases p5976_3 (m.d 0 2) (by simp) with h5981 | h5981
                                            · rcases p5976_3 (m.d 1 2) (by simp) with h5982 | h5982
                                              · linarith only [h0, h5982, hlam]
                                              · linarith only [h5880, h5982, hlam]
                                            · linarith only [h5981, hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h0, hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5876, hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5878, hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h0, h1, h5876, h5884, h5886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5976_1]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5411, h5880, h5884, h5886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5887_1, p5976_1]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            rcases p5976_3 (m.d 0 2) (by simp) with h5992 | h5992
                                            · linarith only [h5412, h5992, hlam]
                                            · linarith only [h0, h5992, hlam]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5411, h5414, h5880, h5884, h5886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5887_1, p5976_1]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h0, h1, h5411, h5876, h5880, hlam, p5887_1, p5976_2]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5411, h5880, h5884, h5886, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5887_1, p5976_1]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            rcases p5976_3 (m.d 0 2) (by simp) with h5999 | h5999
                                            · linarith only [h5414, h5999, hlam]
                                            · linarith only [h0, h5999, hlam]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5883, hlam, p5976_1]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5411, h5414, h5880, hlam, p5887_1, p5976_2]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5872, hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5880, hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5884, hlam, p5976_1]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [h5885, hlam, p5976_0]
                                          · have p5976_0 := h5976c.1
                                            have p5976_1 := h5976c.2.1
                                            have p5976_2 := h5976c.2.2.1
                                            have p5976_3 := h5976c.2.2.2
                                            linarith only [hlam, p5976_0]
                                        · rcases h2bigk with h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c | h6010c
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5414, hc12, hc24, hlam, hphi, p6010_1]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5412, hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5414, hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            rcases p6010_3 (m.d 0 2) (by simp) with h6015 | h6015
                                            · rcases p6010_3 (m.d 1 2) (by simp) with h6016 | h6016
                                              · linarith only [h0, h6016, hlam]
                                              · linarith only [h5880, h6016, hlam]
                                            · linarith only [h6015, hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h0, hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5876, hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5878, hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h0, h1, h5876, h5884, h5886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6010_1]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5411, h5880, h5884, h5886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5887_1, p6010_1]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            rcases p6010_3 (m.d 0 2) (by simp) with h6026 | h6026
                                            · linarith only [h5412, h6026, hlam]
                                            · linarith only [h0, h6026, hlam]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5411, h5414, h5880, h5884, h5886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5887_1, p6010_1]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h0, h1, h5411, h5876, h5880, hlam, p5887_1, p6010_2]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5411, h5880, h5884, h5886, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5887_1, p6010_1]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            rcases p6010_3 (m.d 0 2) (by simp) with h6033 | h6033
                                            · linarith only [h5414, h6033, hlam]
                                            · linarith only [h0, h6033, hlam]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5883, hlam, p6010_1]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5411, h5414, h5880, hlam, p5887_1, p6010_2]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5872, hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5880, hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5884, hlam, p6010_1]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [h5885, hlam, p6010_0]
                                          · have p6010_0 := h6010c.1
                                            have p6010_1 := h6010c.2.1
                                            have p6010_2 := h6010c.2.2.1
                                            have p6010_3 := h6010c.2.2.2
                                            linarith only [hlam, p6010_0]
                                        · linarith only [h5410, h5414, h5907, hlam, p5887_1, u0elo0]
                                    · linarith only [h5875, h5904, hlam]
                                  · linarith only [h5874, h5903, hlam]
                                · linarith only [h5872, h5902, hlam]
                              · linarith only [h5411, h5901, hlam]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h5410, h5878, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5887_1, u0elo2]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h5872, h5884, h5886, hc45, hlam, hphi, ht0b, ht5b, p5887_1, u0elo2]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [hlam, p5887_0]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h5414, h5872, h5884, h5886, hc45, hlam, hphi, ht0b, ht5b, p5887_1, u0elo2]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              rcases p5887_3 (m.d 0 1) (by simp) with h6053 | h6053
                              · linarith only [h1, h6053, hlam]
                              · linarith only [h5411, h6053, hlam]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h5410, hlam, p5887_0]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h0, h5880, h5884, h5886, hc45, hlam, hphi, ht0b, ht5b, p5887_1, u0elo3]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h5873, hlam, p5887_0]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [hlam, p5887_0]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              rcases p5887_3 (m.d 0 1) (by simp) with h6060 | h6060
                              · rcases p5887_3 (m.d 0 2) (by simp) with h6061 | h6061
                                · linarith only [h5414, h6061, hlam]
                                · linarith only [h5872, h6061, hlam]
                              · linarith only [h5411, h6060, hlam]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h5411, hlam, p5887_0]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h5872, hlam, p5887_1]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h5874, hlam, p5887_0]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [h5875, hlam, p5887_1]
                            · have p5887_0 := h5887c.1
                              have p5887_1 := h5887c.2.1
                              have p5887_2 := h5887c.2.2.1
                              have p5887_3 := h5887c.2.2.2
                              linarith only [hlam, p5887_0]
                          · linarith only [h1, h5410, h5876, h5882, h5886, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h1, h5410, h5876, h5882, h5885, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1, h5410, h5876, h5878, h5884, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h5410, h5876, h5878, h5880, h5883, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h5410, h5875, h5878, h5880, h5882, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h1, h5410, h5878, h5880, h5881, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · linarith only [h5414, h5872, h5880, hc12, hc24, hlam, hphi]
        · linarith only [h5414, h5872, h5875, hlam]
      · linarith only [h1, h5410, h5414, h5872, h5874, hlam]
    · linarith only [h1, h5410, h5873, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6080 | h6080
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6081 | h6081
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6082 | h6082
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6083 | h6083
          · linarith only [h0, h5412, h6083, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6085 | h6085
            · linarith only [h0, h5414, h6085, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6087 | h6087
              · linarith only [h0, h5872, h6087, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6089 | h6089
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6090 | h6090
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6091 | h6091
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6092 | h6092
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6093 | h6093
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6094 | h6094
                          · rcases h0bigk with h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c | h6095c
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [hlam, p6095_0]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h0, h1, h6083, hc12, hc23, hlam, hphi, p6095_1]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h1, hlam, p6095_0]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h1, h5410, h6083, h6089, h6094, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6095_1]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h0, h1, h5872, h6083, hc12, hc23, hlam, hphi, p6095_1]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h0, hlam, p6095_0]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [hlam, p6095_0]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h5412, hlam, p6095_0]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h5414, hlam, p6095_1]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h5872, hlam, p6095_0]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6095_1, u0elo2]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              rcases p6095_3 (m.d 0 1) (by simp) with h6107 | h6107
                              · linarith only [h1, h6107, hlam]
                              · linarith only [h0, h6107, hlam]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [hlam, p6095_0]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h5410, h6089, h6094, hc45, hlam, hphi, ht0b, ht5b, p6095_1, u0elo2]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              rcases p6095_3 (m.d 0 1) (by simp) with h6112 | h6112
                              · linarith only [h1, h6112, hlam]
                              · linarith only [h5411, h6112, hlam]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h5410, hlam, p6095_0]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h0, h1, h5410, h6083, hc12, hc23, hlam, hphi, p6095_1]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h6080, hlam, p6095_0]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [hlam, p6095_0]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h0, h1, h5410, h5872, h6083, hc12, hc23, hlam, hphi, p6095_1]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h5411, hlam, p6095_0]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h0, h1, h5411, h6083, hc12, hc23, hlam, hphi, p6095_1]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h6081, hlam, p6095_0]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [h6082, hlam, p6095_1]
                            · have p6095_0 := h6095c.1
                              have p6095_1 := h6095c.2.1
                              have p6095_2 := h6095c.2.2.1
                              have p6095_3 := h6095c.2.2.2
                              linarith only [hlam, p6095_0]
                          · linarith only [h1, h5410, h6083, h6090, h6094, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1, h5410, h5414, h6083, h6090, h6093, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h5410, h6081, h6082, h6083, h6092, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h1, h5410, h6083, h6090, h6091, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h1, h5410, h6082, h6083, h6085, h6090, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h6089, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6131 | h6131
          · linarith only [h0, h5412, h6131, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6133 | h6133
            · linarith only [h0, h5414, h6133, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6135 | h6135
              · linarith only [h0, h5872, h6135, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6137 | h6137
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6138 | h6138
                  · linarith only [h5410, h6082, h6138, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6140 | h6140
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6141 | h6141
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6142 | h6142
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6143 | h6143
                          · linarith only [h5410, h6082, h6137, h6143, hlam]
                          · rcases h0bigk with h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c | h6145c
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h1, h6131, hc02, hc23, hlam, hphi, p6145_1]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h1, hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h0, h1, h5414, h6131, hc12, hc23, hlam, hphi, p6145_1]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h0, h1, h5872, h6131, hc12, hc23, hlam, hphi, p6145_1]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h0, hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h5412, hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h5414, hlam, p6145_1]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h5872, hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6145_1, u0elo2]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              rcases p6145_3 (m.d 0 1) (by simp) with h6157 | h6157
                              · linarith only [h1, h6157, hlam]
                              · linarith only [h0, h6157, hlam]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              rcases p6145_3 (m.d 0 1) (by simp) with h6161 | h6161
                              · linarith only [h1, h6161, hlam]
                              · linarith only [h5410, h6161, hlam]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              rcases p6145_3 (m.d 0 1) (by simp) with h6164 | h6164
                              · linarith only [h1, h6164, hlam]
                              · linarith only [h5411, h6164, hlam]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h5410, hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h0, h6082, hc12, hc45, hlam, hphi, ht23, ht34, p6145_1]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h6080, hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h6082, hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h5411, hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h0, h1, h5411, h6131, hc12, hc23, hlam, hphi, p6145_1]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h6081, hlam, p6145_0]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [h0, h1, h5411, h5414, h6131, hc12, hc23, hlam, hphi, p6145_1]
                            · have p6145_0 := h6145c.1
                              have p6145_1 := h6145c.2.1
                              have p6145_2 := h6145c.2.2.1
                              have p6145_3 := h6145c.2.2.2
                              linarith only [hlam, p6145_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6177 | h6177
                          · linarith only [h1, h5410, h6131, h6137, h6142, h6177, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases h0bigk with h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h0, h1, h6131, hc12, hc23, hlam, hphi, p6179_1]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h1, hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h0, h1, h5414, h6131, hc12, hc23, hlam, hphi, p6179_1]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h0, h1, h5872, h6131, hc12, hc23, hlam, hphi, p6179_1]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h0, hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h5412, hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h5414, hlam, p6179_1]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h5872, hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6179_1, u0elo2]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              rcases p6179_3 (m.d 0 1) (by simp) with h6191 | h6191
                              · linarith only [h1, h6191, hlam]
                              · linarith only [h0, h6191, hlam]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              rcases p6179_3 (m.d 0 1) (by simp) with h6195 | h6195
                              · linarith only [h1, h6195, hlam]
                              · linarith only [h5410, h6195, hlam]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              rcases p6179_3 (m.d 0 1) (by simp) with h6198 | h6198
                              · linarith only [h1, h6198, hlam]
                              · linarith only [h5411, h6198, hlam]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h5410, hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h0, h1, h5410, h6131, hc12, hc23, hlam, hphi, p6179_1]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h6080, hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h6082, hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h5411, hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h0, h1, h5411, h6131, hc12, hc23, hlam, hphi, p6179_1]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h6081, hlam, p6179_0]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [h0, h1, h5411, h5414, h6131, hc12, hc23, hlam, hphi, p6179_1]
                            · have p6179_0 := h6179c.1
                              have p6179_1 := h6179c.2.1
                              have p6179_2 := h6179c.2.2.1
                              have p6179_3 := h6179c.2.2.2
                              linarith only [hlam, p6179_0]
                      · linarith only [h1, h6081, h6131, h6141, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1, h5411, h6131, h6137, h6138, h6140, hlam]
                · linarith only [h0, h1, h6137, hc12, hc34, hlam, hphi, ht23]
      · linarith only [h1, h5411, h6081, hlam]
    · linarith only [h1, h5410, h6080, hlam]

set_option maxHeartbeats 13584000 in
set_option maxHeartbeats 13584000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h5410 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h5412 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h5414 | h5414
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0_x0_x1_x0 m hb0 hb2 hb4 hg0 h1 h5410 h5411 h5412 h5414
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0_x0_x1_x1 m hb0 hb2 hb4 hg0 h1 h5410 h5411 h5412 h5414

set_option maxHeartbeats 13584000 in
set_option maxHeartbeats 13584000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h5410 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h5412 | h5412
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0_x0_x0 m hb0 hb2 hb4 hg0 h1 h5410 h5411 h5412
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0_x0_x1 m hb0 hb2 hb4 hg0 h1 h5410 h5411 h5412

set_option maxHeartbeats 13584000 in
set_option maxHeartbeats 13584000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h5410 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5411 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h6216 | h6216
  · linarith only [h0, h1, h6216, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h6218 | h6218
    · rcases m.htr 0 2 5 (by decide) (by decide) with h6219 | h6219
      · linarith only [h0, h5411, h6219, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6221 | h6221
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6222 | h6222
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6223 | h6223
            · linarith only [h0, h5411, h6218, h6223, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6225 | h6225
              · linarith only [h0, h6216, h6225, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6227 | h6227
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6228 | h6228
                  · linarith only [h0, h5411, h6219, h6228, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6230 | h6230
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6231 | h6231
                      · linarith only [h0, h5410, h5411, h6218, h6223, h6227, h6231, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h5411, h6227, h6231, hc24, hc45, hlam, hphi]
                    · linarith only [h0, h1, h6227, h6230, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h6218, h6225, h6227, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6236 | h6236
            · linarith only [h5410, h5411, h6236, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6238 | h6238
              · linarith only [h0, h1, h6222, h6238, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6240 | h6240
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6241 | h6241
                  · linarith only [h0, h1, h6219, h6222, h6241, hc02, hc35, hlam, hphi, ht23]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6243 | h6243
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6244 | h6244
                      · linarith only [h1, h5410, h6222, h6236, h6244, hlam]
                      · linarith only [h0, h5411, h6240, h6244, hc24, hc45, hlam, hphi]
                    · linarith only [h0, h1, h6218, h6221, h6240, h6243, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h0, h1, h6218, h6238, h6240, hc12, hc23, hlam, hphi]
        · linarith only [h0, h1, h6218, h6221, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h6250 | h6250
      · linarith only [h5410, h5411, h6218, h6250, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6252 | h6252
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6253 | h6253
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6254 | h6254
            · linarith only [h5410, h5411, h6254, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6256 | h6256
              · linarith only [h0, h6216, h6252, h6256, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6258 | h6258
                · linarith only [h0, h6218, h6258, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6260 | h6260
                  · linarith only [h0, h5411, h6250, h6260, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6262 | h6262
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6263 | h6263
                      · linarith only [h5410, h6254, h6263, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6265 | h6265
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6266 | h6266
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6267 | h6267
                            · linarith only [h5410, h5411, h6258, h6263, h6267, hc12, hc24, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6269 | h6269
                              · linarith only [h0, h6218, h6267, h6269, hc12, hc34, hlam, hphi, ht23]
                              · rcases h0bigk with h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [hlam, p6271_0]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h0, h5411, h6260, hc12, hc25, hlam, hphi, p6271_1]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h1, hlam, p6271_0]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h5411, h6260, h6267, hc04, hc45, hlam, hphi, p6271_1]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h5411, hlam, p6271_1]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h0, hlam, p6271_0]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [hlam, p6271_0]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h6216, hlam, p6271_0]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h6218, hlam, p6271_1]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h6250, hlam, p6271_0]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6271_1, u0elo2]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  rcases p6271_3 (m.d 0 1) (by simp) with h6283 | h6283
                                  · linarith only [h1, h6283, hlam]
                                  · linarith only [h0, h6283, hlam]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [hlam, p6271_0]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  rcases p6271_3 (m.d 0 1) (by simp) with h6287 | h6287
                                  · linarith only [h1, h6287, hlam]
                                  · linarith only [h5410, h6287, hlam]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h5410, h5411, h6258, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6271_1, u0elo2]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h5410, hlam, p6271_0]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h0, h1, h5410, h6256, hc12, hc23, hlam, hphi, p6271_1]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h6252, hlam, p6271_0]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [hlam, p6271_0]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h6254, hlam, p6271_0]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6271_1, u0elo4]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  rcases p6271_3 (m.d 0 1) (by simp) with h6297 | h6297
                                  · linarith only [h5411, h6297, hlam]
                                  · linarith only [h0, h6297, hlam]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [h6253, hlam, p6271_0]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  rcases p6271_3 (m.d 0 1) (by simp) with h6301 | h6301
                                  · linarith only [h5411, h6301, hlam]
                                  · linarith only [h5410, h6301, hlam]
                                · have p6271_0 := h6271c.1
                                  have p6271_1 := h6271c.2.1
                                  have p6271_2 := h6271c.2.2.1
                                  have p6271_3 := h6271c.2.2.2
                                  linarith only [hlam, p6271_0]
                          · linarith only [h1, h5410, h6253, h6256, h6258, h6266, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1, h5410, h6256, h6258, h6265, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h5410, h6252, h6258, h6262, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6308 | h6308
            · linarith only [h5410, h5411, h6308, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6310 | h6310
              · linarith only [h0, h1, h6253, h6310, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6312 | h6312
                · linarith only [h0, h6218, h6312, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6314 | h6314
                  · linarith only [h0, h6250, h6314, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6316 | h6316
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6317 | h6317
                      · linarith only [h1, h5410, h6253, h6308, h6317, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6319 | h6319
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6320 | h6320
                          · linarith only [h1, h5410, h6253, h6312, h6320, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h5410, h6310, h6312, h6320, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h5410, h6310, h6316, h6319, hlam]
                    · linarith only [h1, h5410, h6312, h6316, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1, h5410, h6252, hlam]

set_option maxHeartbeats 13584000 in
set_option maxHeartbeats 13584000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h5410 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h5411 | h5411
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0_x0 m hb0 hb2 hb4 hg0 h1 h5410 h5411
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0_x1 m hb0 hb2 hb4 hg0 h1 h5410 h5411

end R2N4
