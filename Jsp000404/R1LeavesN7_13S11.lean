import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8662 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8663 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8664 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 3 5 (by decide) (by decide) with h9931 | h9931
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9932 | h9932
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9933 | h9933
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9934 | h9934
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9935 | h9935
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9936 | h9936
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9937 | h9937
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9938 | h9938
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9939 | h9939
                  · linarith only [h8661, h8664, h9939, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9941 | h9941
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9942 | h9942
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9943 | h9943
                        · rcases h2bigk with h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c | h9944c
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h0, hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h9941, h9943, hc02, hc45, hlam, hphi, ht0b, ht5b, p9944_1]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h0, h9939, h9941, h9943, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9944_1]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            rcases p9944_3 (m.d 0 2) (by simp) with h9949 | h9949
                            · rcases p9944_3 (m.d 1 2) (by simp) with h9950 | h9950
                              · rcases p9944_3 (m.d 2 3) (by simp) with h9951 | h9951
                                · linarith only [h8661, h9951, hlam]
                                · linarith only [h9941, h9951, hlam]
                              · linarith only [h9935, h9950, hlam]
                            · linarith only [h9949, hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9944_1]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h9941, h9943, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9944_1]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h9939, h9941, h9943, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9944_1]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            rcases p9944_3 (m.d 0 2) (by simp) with h9960 | h9960
                            · linarith only [h0, h9960, hlam]
                            · linarith only [h8663, h9960, hlam]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h8661, hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h9933, hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h9939, hlam, p9944_1]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h8662, h9939, h9941, h9943, hc02, hc45, hlam, hphi, ht0b, ht5b, p9944_1]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h8662, hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h9934, hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h8662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9944_1]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h8662, h8664, h9936, h9941, h9943, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p9944_1]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h8663, hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h9935, hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h9941, hlam, p9944_0]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [h9942, hlam, p9944_1]
                          · have p9944_0 := h9944c.1
                            have p9944_1 := h9944c.2.1
                            have p9944_2 := h9944c.2.2.1
                            have p9944_3 := h9944c.2.2.2
                            linarith only [hlam, p9944_0]
                        · linarith only [h8664, h9932, h9943, hlam]
                      · linarith only [h8664, h9931, h9932, h9933, h9936, h9939, h9941, h9942, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h8664, h9931, h9933, h9936, h9941, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h8664, h9931, h9932, h9936, h9938, hlam]
              · linarith only [h8664, h9931, h9936, h9937, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9983 | h9983
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9984 | h9984
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9985 | h9985
                  · linarith only [h7870, h9936, h9983, h9985, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9987 | h9987
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9988 | h9988
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9989 | h9989
                        · rcases h2bigk with h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c | h9990c
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h0, hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h0, h9987, h9989, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9990_1]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h0, h9985, h9987, h9989, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9990_1]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            rcases p9990_3 (m.d 0 2) (by simp) with h9995 | h9995
                            · rcases p9990_3 (m.d 1 2) (by simp) with h9996 | h9996
                              · rcases p9990_3 (m.d 2 3) (by simp) with h9997 | h9997
                                · linarith only [h8661, h9997, hlam]
                                · linarith only [h9987, h9997, hlam]
                              · linarith only [h9935, h9996, hlam]
                            · linarith only [h9995, hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9990_1]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h9987, h9989, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9990_1]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h9985, h9987, h9989, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9990_1]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            rcases p9990_3 (m.d 0 2) (by simp) with h10006 | h10006
                            · linarith only [h0, h10006, hlam]
                            · linarith only [h10006, h8663, hlam]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h8661, hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h9933, hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h9985, hlam, p9990_1]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h8661, h9987, h9989, hc02, hc45, hlam, hphi, ht0b, ht5b, p9990_1]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h8662, hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h9934, hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h0, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9990_1]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h0, h8662, h9987, h9989, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9990_1]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h8663, hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h9935, hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h9987, hlam, p9990_0]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [h9988, hlam, p9990_1]
                          · have p9990_0 := h9990c.1
                            have p9990_1 := h9990c.2.1
                            have p9990_2 := h9990c.2.2.1
                            have p9990_3 := h9990c.2.2.2
                            linarith only [hlam, p9990_0]
                        · linarith only [h7870, h9936, h9983, h9989, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h9985, h9987, h9988, hlam]
                    · linarith only [h5135, h9931, h9936, h9987, hc23, hc34, hlam, hphi]
                · linarith only [h5135, h6923, h9931, h9932, h9936, h9984, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h5135, h9931, h9983, hlam]
          · linarith only [h0, h8663, h9935, hlam]
        · linarith only [h0, h8662, h9934, hlam]
      · linarith only [h0, h8661, h9933, hlam]
    · linarith only [h8664, h9931, h9932, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h10033 | h10033
    · rcases m.htr 1 2 3 (by decide) (by decide) with h10034 | h10034
      · rcases m.htr 1 2 4 (by decide) (by decide) with h10035 | h10035
        · rcases m.htr 1 2 5 (by decide) (by decide) with h10036 | h10036
          · rcases m.htr 1 3 4 (by decide) (by decide) with h10037 | h10037
            · rcases m.htr 1 3 5 (by decide) (by decide) with h10038 | h10038
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10039 | h10039
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10040 | h10040
                  · linarith only [h10040, h8661, h8664, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10042 | h10042
                    · linarith only [h10042, h8661, h9931, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10044 | h10044
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10045 | h10045
                        · rcases h2bigk with h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c | h10046c
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h0, hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            rcases p10046_3 (m.d 0 2) (by simp) with h10049 | h10049
                            · rcases p10046_3 (m.d 1 2) (by simp) with h10050 | h10050
                              · rcases p10046_3 (m.d 2 3) (by simp) with h10051 | h10051
                                · linarith only [h10051, hlam, p10046_0]
                                · rcases p10046_3 (m.d 2 4) (by simp) with h10053 | h10053
                                  · linarith only [h10053, h8662, hlam]
                                  · linarith only [h10040, h10053, hlam]
                              · linarith only [h10034, h10050, hlam]
                            · linarith only [h10049, hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h0, h10044, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10046_1]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            rcases p10046_3 (m.d 0 2) (by simp) with h10059 | h10059
                            · rcases p10046_3 (m.d 1 2) (by simp) with h10060 | h10060
                              · rcases p10046_3 (m.d 2 3) (by simp) with h10061 | h10061
                                · linarith only [h10061, h8661, hlam]
                                · rcases p10046_3 (m.d 2 4) (by simp) with h10063 | h10063
                                  · linarith only [h10063, h8662, hlam]
                                  · linarith only [h10044, h10063, hlam]
                              · linarith only [h10036, h10060, hlam]
                            · linarith only [h10059, hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p10046_1]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            rcases p10046_3 (m.d 0 2) (by simp) with h10070 | h10070
                            · linarith only [h0, h10070, hlam]
                            · linarith only [h10070, h8661, hlam]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h10044, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10046_1]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            rcases p10046_3 (m.d 0 2) (by simp) with h10074 | h10074
                            · linarith only [h0, h10074, hlam]
                            · linarith only [h10074, h8663, hlam]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h8661, hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h10034, hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h10040, hlam, p10046_1]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h10042, hlam, p10046_1]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h8662, hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h10035, hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h8662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10046_1]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h0, h10042, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10046_1]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h8663, hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h10036, hlam, p10046_0]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h0, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10046_1]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [h10044, hlam, p10046_1]
                          · have p10046_0 := h10046c.1
                            have p10046_1 := h10046c.2.1
                            have p10046_2 := h10046c.2.2.1
                            have p10046_3 := h10046c.2.2.2
                            linarith only [hlam, p10046_0]
                        · linarith only [h10033, h10045, h8664, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10093 | h10093
                        · rcases h2bigk with h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c | h10094c
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h0, hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            rcases p10094_3 (m.d 0 2) (by simp) with h10097 | h10097
                            · rcases p10094_3 (m.d 1 2) (by simp) with h10098 | h10098
                              · rcases p10094_3 (m.d 2 3) (by simp) with h10099 | h10099
                                · linarith only [h10099, hlam, p10094_0]
                                · rcases p10094_3 (m.d 2 4) (by simp) with h10101 | h10101
                                  · linarith only [h10101, h8662, hlam]
                                  · linarith only [h10040, h10101, hlam]
                              · linarith only [h10034, h10098, hlam]
                            · linarith only [h10097, hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            rcases p10094_3 (m.d 0 2) (by simp) with h10106 | h10106
                            · rcases p10094_3 (m.d 1 2) (by simp) with h10107 | h10107
                              · rcases p10094_3 (m.d 2 3) (by simp) with h10108 | h10108
                                · linarith only [h10108, h8661, hlam]
                                · rcases p10094_3 (m.d 2 4) (by simp) with h10110 | h10110
                                  · linarith only [h10110, hlam, p10094_0]
                                  · rcases p10094_3 (m.d 2 5) (by simp) with h10112 | h10112
                                    · linarith only [h10112, h8663, hlam]
                                    · linarith only [h10044, h10112, hlam]
                              · linarith only [h10035, h10107, hlam]
                            · linarith only [h10106, hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            rcases p10094_3 (m.d 0 2) (by simp) with h10117 | h10117
                            · rcases p10094_3 (m.d 1 2) (by simp) with h10118 | h10118
                              · rcases p10094_3 (m.d 2 3) (by simp) with h10119 | h10119
                                · linarith only [h10119, h8661, hlam]
                                · rcases p10094_3 (m.d 2 4) (by simp) with h10121 | h10121
                                  · linarith only [h10121, h8662, hlam]
                                  · rcases p10094_3 (m.d 2 5) (by simp) with h10123 | h10123
                                    · linarith only [h10123, hlam, p10094_0]
                                    · rcases h3bigk with h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c | h10125c
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [hlam, p10125_0]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h5135, hlam, p10125_1]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h9931, hc23, hc35, hlam, hphi, p10125_1]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h8664, hlam, p10125_0]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h9931, hlam, p10125_0]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        rcases p10125_3 (m.d 0 3) (by simp) with h10131 | h10131
                                        · linarith only [h10131, h5135, hlam]
                                        · rcases p10125_3 (m.d 1 3) (by simp) with h10133 | h10133
                                          · rcases p10125_3 (m.d 2 3) (by simp) with h10134 | h10134
                                            · linarith only [h10034, h10134, hlam]
                                            · rcases p10125_3 (m.d 3 4) (by simp) with h10136 | h10136
                                              · linarith only [h10037, h10136, hlam]
                                              · linarith only [h10136, h8664, hlam]
                                          · linarith only [h10133, h5135, hlam]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [hlam, p10125_0]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h10033, h10037, h10040, h10044, h8664, hlam, p10125_2]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h10033, h10034, h10044, h8664, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10125_1]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h10034, h5135, h9931, hc01, hc12, hlam, hphi, p10125_1]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h8661, hlam, p10125_1]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h10034, hlam, p10125_1]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [hlam, p10125_0]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h10040, hlam, p10125_0]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h10042, hlam, p10125_0]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h10034, h10037, h5135, hc01, hc12, hlam, hphi, p10125_1]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h10037, hlam, p10125_0]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        rcases p10125_3 (m.d 0 3) (by simp) with h10151 | h10151
                                        · linarith only [h10151, h8664, hlam]
                                        · linarith only [h10151, h8661, hlam]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [hlam, p10125_0]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h10034, h10037, h7870, h9931, hc01, hc12, hlam, hphi, p10125_1]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h10034, h10038, h5135, hc01, hc12, hlam, hphi, p10125_1]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h10038, hlam, p10125_0]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        rcases p10125_3 (m.d 0 3) (by simp) with h10158 | h10158
                                        · linarith only [h10158, h9931, hlam]
                                        · linarith only [h10158, h8661, hlam]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [h10093, hlam, p10125_1]
                                      · have p10125_0 := h10125c.1
                                        have p10125_1 := h10125c.2.1
                                        have p10125_2 := h10125c.2.2.1
                                        have p10125_3 := h10125c.2.2.2
                                        linarith only [hlam, p10125_0]
                              · linarith only [h10036, h10118, hlam]
                            · linarith only [h10117, hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p10094_1]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            rcases p10094_3 (m.d 0 2) (by simp) with h10167 | h10167
                            · linarith only [h0, h10167, hlam]
                            · linarith only [h10167, h8661, hlam]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            rcases p10094_3 (m.d 0 2) (by simp) with h10170 | h10170
                            · linarith only [h0, h10170, hlam]
                            · linarith only [h10170, h8662, hlam]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            rcases p10094_3 (m.d 0 2) (by simp) with h10173 | h10173
                            · linarith only [h0, h10173, hlam]
                            · linarith only [h10173, h8663, hlam]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h8661, hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h10034, hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h10040, hlam, p10094_1]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h10042, hlam, p10094_1]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h8662, hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h10035, hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h10033, h10044, h8662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10094_1]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h10044, hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h8663, hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h10036, hlam, p10094_0]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h0, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10094_1]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [h10033, h10034, h10037, h10044, h8664, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10094_1]
                          · have p10094_0 := h10094c.1
                            have p10094_1 := h10094c.2.1
                            have p10094_2 := h10094c.2.2.1
                            have p10094_3 := h10094c.2.2.2
                            linarith only [hlam, p10094_0]
                        · linarith only [h10033, h10093, h8664, hlam]
                · linarith only [h10033, h10034, h10037, h10039, h6923, h8664, hc01, hc12, hlam, hphi]
              · linarith only [h10037, h10038, h5135, h8664, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h10194 | h10194
              · linarith only [h10037, h10194, h5135, h9931, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10196 | h10196
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10197 | h10197
                  · linarith only [h10037, h10197, h5135, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10199 | h10199
                    · linarith only [h10194, h10199, h5135, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10201 | h10201
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10202 | h10202
                        · rcases h2bigk with h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c | h10203c
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h0, hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            rcases p10203_3 (m.d 0 2) (by simp) with h10206 | h10206
                            · rcases p10203_3 (m.d 1 2) (by simp) with h10207 | h10207
                              · rcases p10203_3 (m.d 2 3) (by simp) with h10208 | h10208
                                · linarith only [h10208, hlam, p10203_0]
                                · rcases p10203_3 (m.d 2 4) (by simp) with h10210 | h10210
                                  · linarith only [h10210, h8662, hlam]
                                  · linarith only [h10197, h10210, hlam]
                              · linarith only [h10034, h10207, hlam]
                            · linarith only [h10206, hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h0, h10201, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10203_1]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            rcases p10203_3 (m.d 0 2) (by simp) with h10216 | h10216
                            · rcases p10203_3 (m.d 1 2) (by simp) with h10217 | h10217
                              · rcases p10203_3 (m.d 2 3) (by simp) with h10218 | h10218
                                · linarith only [h10218, h8661, hlam]
                                · rcases p10203_3 (m.d 2 4) (by simp) with h10220 | h10220
                                  · linarith only [h10220, h8662, hlam]
                                  · linarith only [h10201, h10220, hlam]
                              · linarith only [h10036, h10217, hlam]
                            · linarith only [h10216, hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p10203_1]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            rcases p10203_3 (m.d 0 2) (by simp) with h10227 | h10227
                            · linarith only [h0, h10227, hlam]
                            · linarith only [h10227, h8661, hlam]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h10201, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10203_1]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            rcases p10203_3 (m.d 0 2) (by simp) with h10231 | h10231
                            · linarith only [h0, h10231, hlam]
                            · linarith only [h10231, h8663, hlam]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h8661, hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h10034, hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h10197, hlam, p10203_1]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h10199, hlam, p10203_1]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h8662, hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h10035, hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h8662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10203_1]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h0, h10199, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10203_1]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h8663, hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h10036, hlam, p10203_0]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h0, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10203_1]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [h10201, hlam, p10203_1]
                          · have p10203_0 := h10203c.1
                            have p10203_1 := h10203c.2.1
                            have p10203_2 := h10203c.2.2.1
                            have p10203_3 := h10203c.2.2.2
                            linarith only [hlam, p10203_0]
                        · linarith only [h10033, h10037, h10202, h6923, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10250 | h10250
                        · rcases h2bigk with h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h0, hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            rcases p10251_3 (m.d 0 2) (by simp) with h10254 | h10254
                            · rcases p10251_3 (m.d 1 2) (by simp) with h10255 | h10255
                              · rcases p10251_3 (m.d 2 3) (by simp) with h10256 | h10256
                                · linarith only [h10256, hlam, p10251_0]
                                · rcases p10251_3 (m.d 2 4) (by simp) with h10258 | h10258
                                  · linarith only [h10258, h8662, hlam]
                                  · linarith only [h10197, h10258, hlam]
                              · linarith only [h10034, h10255, hlam]
                            · linarith only [h10254, hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            rcases p10251_3 (m.d 0 2) (by simp) with h10263 | h10263
                            · rcases p10251_3 (m.d 1 2) (by simp) with h10264 | h10264
                              · rcases p10251_3 (m.d 2 3) (by simp) with h10265 | h10265
                                · linarith only [h10265, h8661, hlam]
                                · rcases p10251_3 (m.d 2 4) (by simp) with h10267 | h10267
                                  · linarith only [h10267, hlam, p10251_0]
                                  · rcases p10251_3 (m.d 2 5) (by simp) with h10269 | h10269
                                    · linarith only [h10269, h8663, hlam]
                                    · linarith only [h10201, h10269, hlam]
                              · linarith only [h10035, h10264, hlam]
                            · linarith only [h10263, hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            rcases p10251_3 (m.d 0 2) (by simp) with h10274 | h10274
                            · rcases p10251_3 (m.d 1 2) (by simp) with h10275 | h10275
                              · rcases p10251_3 (m.d 2 3) (by simp) with h10276 | h10276
                                · linarith only [h10276, h8661, hlam]
                                · rcases p10251_3 (m.d 2 4) (by simp) with h10278 | h10278
                                  · linarith only [h10278, h8662, hlam]
                                  · rcases p10251_3 (m.d 2 5) (by simp) with h10280 | h10280
                                    · linarith only [h10280, hlam, p10251_0]
                                    · rcases h3bigk with h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c | h10282c
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [hlam, p10282_0]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h5135, hlam, p10282_1]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h8664, hc23, hc34, hlam, hphi, p10282_1]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h8664, hlam, p10282_0]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h9931, hlam, p10282_0]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h10037, hc03, hc34, hlam, hphi, p10282_1]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [hlam, p10282_0]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h10037, hc23, hc34, hlam, hphi, p10282_1]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h10037, hlam, p10282_0]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h10194, hlam, p10282_0]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h8661, hlam, p10282_1]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h10034, hlam, p10282_1]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [hlam, p10282_0]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h10197, hlam, p10282_0]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h10199, hlam, p10282_0]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        rcases p10282_3 (m.d 0 3) (by simp) with h10298 | h10298
                                        · linarith only [h10298, hlam, p10282_0]
                                        · rcases p10282_3 (m.d 1 3) (by simp) with h10300 | h10300
                                          · linarith only [h10037, h10300, hlam]
                                          · linarith only [h10300, h5135, hlam]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h0, h10197, h10201, h5135, hc01, hc12, hc23, hc34, hlam, hphi, p10251_1, p10282_1]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        rcases p10282_3 (m.d 0 3) (by simp) with h10304 | h10304
                                        · linarith only [h10304, h8664, hlam]
                                        · linarith only [h10304, h8661, hlam]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [hlam, p10282_0]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h0, h10194, h10197, h10201, h7870, hc01, hc12, hc23, hc34, hlam, hphi, p10251_1, p10282_1]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        rcases p10282_3 (m.d 0 3) (by simp) with h10309 | h10309
                                        · linarith only [h10309, hlam, p10282_0]
                                        · rcases p10282_3 (m.d 1 3) (by simp) with h10311 | h10311
                                          · linarith only [h10194, h10311, hlam]
                                          · linarith only [h10311, h5135, hlam]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h0, h10197, h10201, h5135, hc01, hc12, hc23, hc35, hlam, hphi, p10251_1, p10282_1]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        rcases p10282_3 (m.d 0 3) (by simp) with h10315 | h10315
                                        · linarith only [h10315, h9931, hlam]
                                        · linarith only [h10315, h8661, hlam]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [h10250, hlam, p10282_1]
                                      · have p10282_0 := h10282c.1
                                        have p10282_1 := h10282c.2.1
                                        have p10282_2 := h10282c.2.2.1
                                        have p10282_3 := h10282c.2.2.2
                                        linarith only [hlam, p10282_0]
                              · linarith only [h10036, h10275, hlam]
                            · linarith only [h10274, hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p10251_1]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            rcases p10251_3 (m.d 0 2) (by simp) with h10324 | h10324
                            · linarith only [h0, h10324, hlam]
                            · linarith only [h10324, h8661, hlam]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            rcases p10251_3 (m.d 0 2) (by simp) with h10327 | h10327
                            · linarith only [h0, h10327, hlam]
                            · linarith only [h10327, h8662, hlam]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            rcases p10251_3 (m.d 0 2) (by simp) with h10330 | h10330
                            · linarith only [h0, h10330, hlam]
                            · linarith only [h10330, h8663, hlam]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h8661, hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h10034, hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h10197, hlam, p10251_1]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h10199, hlam, p10251_1]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h8662, hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h10035, hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h10033, h10201, h8662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10251_1]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h10201, hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h8663, hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h10036, hlam, p10251_0]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h8663, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10251_1]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [h10033, h10037, h10201, h6923, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p10251_1]
                          · have p10251_0 := h10251c.1
                            have p10251_1 := h10251c.2.1
                            have p10251_2 := h10251c.2.2.1
                            have p10251_3 := h10251c.2.2.2
                            linarith only [hlam, p10251_0]
                        · linarith only [h10033, h10037, h10250, h6923, hlam]
                · linarith only [h10033, h10196, h6923, hlam]
          · linarith only [h0, h10036, h8663, hlam]
        · linarith only [h0, h10035, h8662, hlam]
      · linarith only [h0, h10034, h8661, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h10353 | h10353
      · rcases m.htr 1 2 4 (by decide) (by decide) with h10354 | h10354
        · rcases m.htr 1 2 5 (by decide) (by decide) with h10355 | h10355
          · rcases m.htr 1 3 4 (by decide) (by decide) with h10356 | h10356
            · rcases m.htr 1 3 5 (by decide) (by decide) with h10357 | h10357
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10358 | h10358
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10359 | h10359
                  · linarith only [h10359, h8661, h8664, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10361 | h10361
                    · linarith only [h10361, h8661, h9931, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10363 | h10363
                      · linarith only [h10033, h10363, h8662, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10365 | h10365
                        · linarith only [h10033, h10353, h10356, h10365, h5135, h8664, hc01, hc12, hlam, hphi]
                        · linarith only [h10358, h10365, h5135, h8664, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10368 | h10368
                  · linarith only [h10368, h8661, h8664, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10370 | h10370
                    · linarith only [h10370, h8661, h9931, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10372 | h10372
                      · linarith only [h10358, h10372, h6923, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10374 | h10374
                        · linarith only [h10356, h10358, h10374, hlam]
                        · rcases h2bigk with h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c | h10376c
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h0, hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            rcases p10376_3 (m.d 0 2) (by simp) with h10379 | h10379
                            · rcases p10376_3 (m.d 1 2) (by simp) with h10380 | h10380
                              · rcases p10376_3 (m.d 2 3) (by simp) with h10381 | h10381
                                · linarith only [h10381, hlam, p10376_0]
                                · rcases p10376_3 (m.d 2 4) (by simp) with h10383 | h10383
                                  · linarith only [h10383, h8662, hlam]
                                  · linarith only [h10368, h10383, hlam]
                              · linarith only [h10353, h10380, hlam]
                            · linarith only [h10379, hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            rcases p10376_3 (m.d 0 2) (by simp) with h10388 | h10388
                            · rcases p10376_3 (m.d 1 2) (by simp) with h10389 | h10389
                              · rcases p10376_3 (m.d 2 3) (by simp) with h10390 | h10390
                                · linarith only [h10390, h8661, hlam]
                                · rcases p10376_3 (m.d 2 4) (by simp) with h10392 | h10392
                                  · linarith only [h10392, hlam, p10376_0]
                                  · rcases p10376_3 (m.d 2 5) (by simp) with h10394 | h10394
                                    · linarith only [h10394, h8663, hlam]
                                    · linarith only [h10372, h10394, hlam]
                              · linarith only [h10354, h10389, hlam]
                            · linarith only [h10388, hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            rcases p10376_3 (m.d 0 2) (by simp) with h10399 | h10399
                            · rcases p10376_3 (m.d 1 2) (by simp) with h10400 | h10400
                              · rcases p10376_3 (m.d 2 3) (by simp) with h10401 | h10401
                                · linarith only [h10401, h8661, hlam]
                                · rcases p10376_3 (m.d 2 4) (by simp) with h10403 | h10403
                                  · linarith only [h10403, h8662, hlam]
                                  · rcases p10376_3 (m.d 2 5) (by simp) with h10405 | h10405
                                    · linarith only [h10405, hlam, p10376_0]
                                    · rcases h3bigk with h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c | h10407c
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [hlam, p10407_0]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h5135, hlam, p10407_1]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h10356, h10358, h8664, hc23, hc45, hlam, hphi, ht34, p10407_1]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h8664, hlam, p10407_0]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h9931, hlam, p10407_0]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        rcases p10407_3 (m.d 0 3) (by simp) with h10413 | h10413
                                        · linarith only [h10413, h5135, hlam]
                                        · rcases p10407_3 (m.d 1 3) (by simp) with h10415 | h10415
                                          · rcases p10407_3 (m.d 2 3) (by simp) with h10416 | h10416
                                            · linarith only [h10353, h10416, hlam]
                                            · rcases p10407_3 (m.d 3 4) (by simp) with h10418 | h10418
                                              · linarith only [h10356, h10418, hlam]
                                              · linarith only [h10418, h8664, hlam]
                                          · linarith only [h10415, h5135, hlam]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [hlam, p10407_0]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        rcases p10407_3 (m.d 0 3) (by simp) with h10423 | h10423
                                        · linarith only [h10423, h5135, hlam]
                                        · linarith only [h10423, h8661, hlam]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h5135, h8664, hc01, hc13, hlam, hphi, p10407_1]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h10353, h5135, h9931, hc01, hc12, hlam, hphi, p10407_1]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h8661, hlam, p10407_1]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h10353, hlam, p10407_1]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [hlam, p10407_0]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h10368, hlam, p10407_0]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h10370, hlam, p10407_0]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h10356, h10358, h5135, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10407_1]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h10356, hlam, p10407_0]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h10356, h10358, hc23, hc45, hlam, hphi, ht34, p10407_1]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [hlam, p10407_0]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h10374, hlam, p10407_0]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h10353, h10357, h5135, hc01, hc12, hlam, hphi, p10407_1]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h10357, hlam, p10407_0]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        rcases p10407_3 (m.d 0 3) (by simp) with h10440 | h10440
                                        · linarith only [h10440, h9931, hlam]
                                        · linarith only [h10440, h8661, hlam]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [h10353, h10357, h6923, h8664, hc01, hc12, hlam, hphi, p10407_1]
                                      · have p10407_0 := h10407c.1
                                        have p10407_1 := h10407c.2.1
                                        have p10407_2 := h10407c.2.2.1
                                        have p10407_3 := h10407c.2.2.2
                                        linarith only [hlam, p10407_0]
                              · linarith only [h10355, h10400, hlam]
                            · linarith only [h10399, hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p10376_1]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            rcases p10376_3 (m.d 0 2) (by simp) with h10449 | h10449
                            · linarith only [h0, h10449, hlam]
                            · linarith only [h10449, h8661, hlam]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            rcases p10376_3 (m.d 0 2) (by simp) with h10452 | h10452
                            · linarith only [h0, h10452, hlam]
                            · linarith only [h10452, h8662, hlam]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            rcases p10376_3 (m.d 0 2) (by simp) with h10455 | h10455
                            · linarith only [h0, h10455, hlam]
                            · linarith only [h10455, h8663, hlam]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h8661, hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h10353, hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h10368, hlam, p10376_1]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h10370, hlam, p10376_1]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h8662, hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h10354, hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h8662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10376_1]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h10372, hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h8663, hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h10355, hlam, p10376_0]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h0, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10376_1]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [h10353, h10357, h8663, h9931, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10376_1]
                          · have p10376_0 := h10376c.1
                            have p10376_1 := h10376c.2.1
                            have p10376_2 := h10376c.2.2.1
                            have p10376_3 := h10376c.2.2.2
                            linarith only [hlam, p10376_0]
              · linarith only [h10356, h10357, h5135, h8664, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h10474 | h10474
              · linarith only [h10356, h10474, h5135, h9931, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10476 | h10476
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10477 | h10477
                  · linarith only [h0, h10356, h10477, h6923, h8661, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10479 | h10479
                    · linarith only [h10033, h10474, h10476, h10479, h5135, h8661, h8664, hc01, hc14, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10481 | h10481
                      · linarith only [h0, h10033, h10481, h5135, h8662, h8664, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10483 | h10483
                        · rcases h2bigk with h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c | h10484c
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h0, hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            rcases p10484_3 (m.d 0 2) (by simp) with h10487 | h10487
                            · rcases p10484_3 (m.d 1 2) (by simp) with h10488 | h10488
                              · rcases p10484_3 (m.d 2 3) (by simp) with h10489 | h10489
                                · linarith only [h10489, hlam, p10484_0]
                                · rcases p10484_3 (m.d 2 4) (by simp) with h10491 | h10491
                                  · linarith only [h10491, h8662, hlam]
                                  · linarith only [h10477, h10491, hlam]
                              · linarith only [h10353, h10488, hlam]
                            · linarith only [h10487, hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            rcases p10484_3 (m.d 0 2) (by simp) with h10496 | h10496
                            · rcases p10484_3 (m.d 1 2) (by simp) with h10497 | h10497
                              · rcases p10484_3 (m.d 2 3) (by simp) with h10498 | h10498
                                · linarith only [h10498, h8661, hlam]
                                · rcases p10484_3 (m.d 2 4) (by simp) with h10500 | h10500
                                  · linarith only [h10500, hlam, p10484_0]
                                  · rcases p10484_3 (m.d 2 5) (by simp) with h10502 | h10502
                                    · linarith only [h10502, h8663, hlam]
                                    · linarith only [h10481, h10502, hlam]
                              · linarith only [h10354, h10497, hlam]
                            · linarith only [h10496, hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            rcases p10484_3 (m.d 0 2) (by simp) with h10507 | h10507
                            · rcases p10484_3 (m.d 1 2) (by simp) with h10508 | h10508
                              · rcases p10484_3 (m.d 2 3) (by simp) with h10509 | h10509
                                · linarith only [h10509, h8661, hlam]
                                · rcases p10484_3 (m.d 2 4) (by simp) with h10511 | h10511
                                  · linarith only [h10511, h8662, hlam]
                                  · rcases p10484_3 (m.d 2 5) (by simp) with h10513 | h10513
                                    · linarith only [h10513, hlam, p10484_0]
                                    · rcases h3bigk with h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c | h10515c
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [hlam, p10515_0]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h5135, hlam, p10515_1]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h10474, h5135, hc23, hc35, hlam, hphi, p10515_1]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h8664, hlam, p10515_0]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h9931, hlam, p10515_0]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h10474, hc03, hc35, hlam, hphi, p10515_1]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [hlam, p10515_0]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h10474, hc23, hc35, hlam, hphi, p10515_1]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h10356, hlam, p10515_0]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h10474, hlam, p10515_0]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h8661, hlam, p10515_1]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h10353, hlam, p10515_1]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [hlam, p10515_0]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h10477, hlam, p10515_0]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h10479, hlam, p10515_0]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        rcases p10515_3 (m.d 0 3) (by simp) with h10531 | h10531
                                        · linarith only [h10531, hlam, p10515_0]
                                        · rcases p10515_3 (m.d 1 3) (by simp) with h10533 | h10533
                                          · linarith only [h10356, h10533, hlam]
                                          · linarith only [h10533, h5135, hlam]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h5135, hc01, hc34, hlam, hphi, ht12, ht23, p10515_1]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        rcases p10515_3 (m.d 0 3) (by simp) with h10537 | h10537
                                        · linarith only [h10537, h8664, hlam]
                                        · linarith only [h10537, h8661, hlam]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [hlam, p10515_0]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h0, h10477, h10481, h5135, h9931, hc01, hc12, hc23, hc34, hlam, hphi, p10484_1, p10515_1]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        rcases p10515_3 (m.d 0 3) (by simp) with h10542 | h10542
                                        · linarith only [h10542, hlam, p10515_0]
                                        · rcases p10515_3 (m.d 1 3) (by simp) with h10544 | h10544
                                          · linarith only [h10474, h10544, hlam]
                                          · linarith only [h10544, h5135, hlam]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h0, h10477, h10481, h5135, hc01, hc12, hc23, hc35, hlam, hphi, p10484_1, p10515_1]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        rcases p10515_3 (m.d 0 3) (by simp) with h10548 | h10548
                                        · linarith only [h10548, h9931, hlam]
                                        · linarith only [h10548, h8661, hlam]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [h10483, hlam, p10515_1]
                                      · have p10515_0 := h10515c.1
                                        have p10515_1 := h10515c.2.1
                                        have p10515_2 := h10515c.2.2.1
                                        have p10515_3 := h10515c.2.2.2
                                        linarith only [hlam, p10515_0]
                              · linarith only [h10355, h10508, hlam]
                            · linarith only [h10507, hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p10484_1]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            rcases p10484_3 (m.d 0 2) (by simp) with h10557 | h10557
                            · linarith only [h0, h10557, hlam]
                            · linarith only [h10557, h8661, hlam]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            rcases p10484_3 (m.d 0 2) (by simp) with h10560 | h10560
                            · linarith only [h0, h10560, hlam]
                            · linarith only [h10560, h8662, hlam]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            rcases p10484_3 (m.d 0 2) (by simp) with h10563 | h10563
                            · linarith only [h0, h10563, hlam]
                            · linarith only [h10563, h8663, hlam]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h8661, hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h10353, hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h10477, hlam, p10484_1]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h10479, hlam, p10484_1]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h8662, hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h10354, hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h10481, h8663, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10484_1]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h10481, hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h8663, hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h10355, hlam, p10484_0]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h10033, h10356, h10476, h8663, hc23, hc34, hlam, hphi, p10484_1]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [h10033, h10356, h10476, h8663, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p10484_1]
                          · have p10484_0 := h10484c.1
                            have p10484_1 := h10484c.2.1
                            have p10484_2 := h10484c.2.2.1
                            have p10484_3 := h10484c.2.2.2
                            linarith only [hlam, p10484_0]
                        · linarith only [h10356, h10476, h10483, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10582 | h10582
                  · linarith only [h10582, h8661, h8664, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10584 | h10584
                    · linarith only [h0, h10584, h5135, h8661, h9931, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10586 | h10586
                      · linarith only [h10476, h10586, h6923, h8662, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10588 | h10588
                        · linarith only [h10356, h10476, h10588, h5135, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h10356, h10588, h5135, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h10355, h8663, hlam]
        · linarith only [h0, h10354, h8662, hlam]
      · linarith only [h0, h10353, h8661, hlam]

set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8662 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8663 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 3 4 (by decide) (by decide) with h8664 | h8664
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h8662 h8663 h8664
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h8662 h8663 h8664

set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8662 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8663 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 3 4 (by decide) (by decide) with h10594 | h10594
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10595 | h10595
    · linarith only [h10595, h8661, h8663, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10597 | h10597
      · linarith only [h10597, h8662, h8663, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10599 | h10599
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10600 | h10600
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10601 | h10601
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10602 | h10602
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10603 | h10603
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10604 | h10604
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10605 | h10605
                    · linarith only [h10601, h10605, h8661, h8663, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h10594, h10601, h10605, h8661, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10608 | h10608
                    · linarith only [h10601, h10608, h8661, h8663, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h10594, h10601, h10608, h8661, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10611 | h10611
                  · linarith only [h10597, h10602, h10603, h10611, h6923, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10613 | h10613
                    · linarith only [h10601, h10613, h8661, h8663, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h10594, h10601, h10613, h8661, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h10594, h10601, h10602, h5135, h8661, h8663, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10617 | h10617
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10618 | h10618
                · linarith only [h10594, h10595, h10599, h10601, h10618, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10620 | h10620
                  · linarith only [h10597, h10599, h10601, h10617, h10620, h6923, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10622 | h10622
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10623 | h10623
                      · linarith only [h10595, h10623, h8661, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10625 | h10625
                        · linarith only [h10620, h10625, h6923, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h10601, h10622, h10625, h8661, hc34, hc45, hlam, hphi]
                    · linarith only [h10594, h10595, h10622, hc23, hc35, hlam, hphi]
              · linarith only [h10594, h10617, h5135, hlam]
          · linarith only [h0, h10600, h8662, hlam]
        · linarith only [h0, h10599, h8661, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10632 | h10632
    · linarith only [h10594, h10632, h8662, h8663, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10634 | h10634
      · linarith only [h10634, h8662, h8663, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10636 | h10636
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10637 | h10637
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10638 | h10638
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10639 | h10639
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10640 | h10640
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10641 | h10641
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10642 | h10642
                    · linarith only [h10594, h10638, h10642, h8661, h8663, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10644 | h10644
                      · linarith only [h10632, h10638, h10642, h10644, h8662, h8663, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10646 | h10646
                        · linarith only [h10636, h10640, h10644, h10646, h8662, h8663, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10648 | h10648
                          · linarith only [h10642, h10646, h10648, h8662, h8663, hc23, hc34, hlam, hphi]
                          · linarith only [h10594, h10636, h10639, h10641, h10648, h5135, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10651 | h10651
                    · linarith only [h10594, h10651, h5135, h8661, h8663, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10653 | h10653
                      · linarith only [h10632, h10638, h10651, h10653, h8662, h8663, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10655 | h10655
                        · linarith only [h10636, h10640, h10641, h10653, h10655, h8662, h8663, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10657 | h10657
                          · linarith only [h10639, h10641, h10657, hlam]
                          · rcases h2bigk with h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c | h10659c
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [hlam, p10659_0]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h0, hlam, p10659_0]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h10636, h10640, h10653, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10659_1]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h10636, h10640, h10653, h8663, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10659_1]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h8663, hlam, p10659_0]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p10659_1]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [hlam, p10659_0]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              rcases p10659_3 (m.d 0 2) (by simp) with h10667 | h10667
                              · linarith only [h0, h10667, hlam]
                              · linarith only [h10667, h8661, hlam]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              rcases p10659_3 (m.d 0 2) (by simp) with h10670 | h10670
                              · linarith only [h0, h10670, hlam]
                              · linarith only [h10670, h8662, hlam]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h10651, h8662, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10659_1]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h8661, hlam, p10659_0]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h10636, hlam, p10659_0]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [hlam, p10659_0]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h10651, hlam, p10659_1]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h10653, hlam, p10659_1]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h8662, hlam, p10659_0]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h10637, hlam, p10659_0]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h8662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10659_1]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [hlam, p10659_0]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h10655, hlam, p10659_0]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [hc02, hc25, hlam, hphi, p10659_1]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h10638, hlam, p10659_0]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h10636, h10640, h10653, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10659_1]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [h10636, h10640, h10653, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10659_1]
                            · have p10659_0 := h10659c.1
                              have p10659_1 := h10659c.2.1
                              have p10659_2 := h10659c.2.2.1
                              have p10659_3 := h10659c.2.2.2
                              linarith only [hlam, p10659_0]
                · linarith only [h10594, h10639, h10640, h5135, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10690 | h10690
                · linarith only [h10632, h10639, h10690, h8661, h8663, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10692 | h10692
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10693 | h10693
                    · linarith only [h10638, h10639, h10693, h8661, h8663, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10695 | h10695
                      · linarith only [h10638, h10690, h10695, h8661, h8663, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10697 | h10697
                        · linarith only [h10594, h10634, h10638, h10697, h5135, h8662, h8663, hc01, hc15, hlam, hphi]
                        · linarith only [h10639, h10692, h10693, h10697, h8662, h8663, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10700 | h10700
                    · linarith only [h10638, h10700, h8661, h8663, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10702 | h10702
                      · linarith only [h10638, h10700, h10702, h8662, h8663, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10704 | h10704
                        · linarith only [h10638, h10704, h8662, h8663, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10706 | h10706
                          · linarith only [h10639, h10692, h10706, h5135, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h10639, h10706, h5135, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10709 | h10709
              · linarith only [h10594, h10636, h10638, h10709, h5135, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10711 | h10711
                · linarith only [h10632, h10637, h10638, h10709, h10711, h5135, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10713 | h10713
                  · linarith only [h10634, h10637, h10638, h10713, h6923, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10715 | h10715
                    · linarith only [h10594, h10715, h8661, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10717 | h10717
                      · linarith only [h10632, h10717, h8661, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10719 | h10719
                        · linarith only [h0, h10638, h10709, h10713, h10717, h10719, h8662, hc13, hc35, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10721 | h10721
                          · linarith only [h0, h10638, h10715, h10719, h10721, h8662, hc23, hc34, hlam, hphi]
                          · linarith only [h10709, h10721, h5135, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h10637, h8662, hlam]
        · linarith only [h0, h10636, h8661, hlam]

set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8662 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 2 5 (by decide) (by decide) with h8663 | h8663
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h8662 h8663
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x1 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h8662 h8663

end R2N4
