import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S16
import Jsp000404.R1LeavesN7_2S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9116000 in
set_option maxHeartbeats 9116000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s11_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h8360 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8361 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  rcases m.htr 0 3 5 (by decide) (by decide) with h8937 | h8937
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8938 | h8938
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8939 | h8939
      · linarith only [h0, h4, h8939, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8941 | h8941
        · linarith only [h0, h7337, h8360, h8941, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8943 | h8943
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8944 | h8944
            · linarith only [h1, h8361, h8944, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8946 | h8946
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8947 | h8947
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8948 | h8948
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8949 | h8949
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8950 | h8950
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8951 | h8951
                        · rcases h0bigk with h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c | h8952c
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [hlam, p8952_0]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            rcases p8952_3 (m.d 0 1) (by simp) with h8954 | h8954
                            · rcases p8952_3 (m.d 0 2) (by simp) with h8955 | h8955
                              · linarith only [h0, h8955, hlam]
                              · rcases p8952_3 (m.d 0 3) (by simp) with h8957 | h8957
                                · linarith only [h1, h8957, hlam]
                                · linarith only [h4, h8957, hlam]
                            · linarith only [h0, h8954, hlam]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            rcases p8952_3 (m.d 0 1) (by simp) with h8961 | h8961
                            · rcases p8952_3 (m.d 0 2) (by simp) with h8962 | h8962
                              · linarith only [h0, h8962, hlam]
                              · rcases p8952_3 (m.d 0 3) (by simp) with h8964 | h8964
                                · linarith only [h1, h8964, hlam]
                                · rcases p8952_3 (m.d 0 4) (by simp) with h8966 | h8966
                                  · linarith only [h2, h8966, hlam]
                                  · linarith only [h8361, h8966, hlam]
                            · linarith only [h1, h8961, hlam]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            rcases p8952_3 (m.d 0 1) (by simp) with h8970 | h8970
                            · rcases p8952_3 (m.d 0 2) (by simp) with h8971 | h8971
                              · linarith only [h0, h8971, hlam]
                              · rcases p8952_3 (m.d 0 3) (by simp) with h8973 | h8973
                                · linarith only [h1, h8973, hlam]
                                · rcases p8952_3 (m.d 0 4) (by simp) with h8975 | h8975
                                  · linarith only [h2, h8975, hlam]
                                  · rcases p8952_3 (m.d 0 5) (by simp) with h8977 | h8977
                                    · linarith only [h3, h8977, hlam]
                                    · rcases h2bigk with h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c | h8979c
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h4, h8361, h8943, h8948, h8949, h8951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8979_1]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h4, hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h7337, hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h4, h8361, h8948, h8949, h8951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8979_1]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h0, hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h8939, hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h8941, hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h0, h4, h8361, h8948, h8949, h8951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8979_1]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        rcases p8979_3 (m.d 0 2) (by simp) with h8990 | h8990
                                        · linarith only [h8990, hlam, p8979_0]
                                        · rcases p8979_3 (m.d 1 2) (by simp) with h8992 | h8992
                                          · linarith only [h8939, h8992, hlam]
                                          · rcases p8979_3 (m.d 2 3) (by simp) with h8994 | h8994
                                            · rcases p8979_3 (m.d 2 4) (by simp) with h8995 | h8995
                                              · linarith only [h8948, h8995, hlam]
                                              · linarith only [h7337, h8995, hlam]
                                            · linarith only [h8994, hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        rcases p8979_3 (m.d 0 2) (by simp) with h8999 | h8999
                                        · linarith only [h4, h8999, hlam]
                                        · linarith only [h0, h8999, hlam]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h4, h8361, h8948, hc02, hc23, hlam, hphi, p8979_1]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h0, h4, h8361, h8943, h8948, hlam, p8979_2]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        rcases p8979_3 (m.d 0 2) (by simp) with h9005 | h9005
                                        · linarith only [h9005, hlam, p8979_0]
                                        · rcases p8979_3 (m.d 1 2) (by simp) with h9007 | h9007
                                          · linarith only [h8941, h9007, hlam]
                                          · rcases p8979_3 (m.d 2 3) (by simp) with h9009 | h9009
                                            · rcases p8979_3 (m.d 2 4) (by simp) with h9010 | h9010
                                              · rcases p8979_3 (m.d 2 5) (by simp) with h9011 | h9011
                                                · linarith only [h8950, h9011, hlam]
                                                · rcases h3bigk with h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c | h9013c
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [hlam, p9013_0]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8939, h8943, h8949, h8951, hc03, hc45, hlam, hphi, ht0b, ht5b, p9013_1]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h4, hlam, p9013_1]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8361, hlam, p9013_0]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8361, h8948, h8951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9013_1]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h1, hlam, p9013_0]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [hlam, p9013_0]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8939, hlam, p9013_1]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8944, hlam, p9013_0]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h1, h8951, hc01, hc45, hlam, hphi, ht0b, ht5b, p9013_1]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h0, h4, h8943, h8949, h8951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9013_1]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8939, h8943, h8949, h8951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9013_1]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [hlam, p9013_0]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h0, h4, h8361, h8943, h8949, h8951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9013_1]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    rcases p9013_3 (m.d 0 3) (by simp) with h9028 | h9028
                                                    · linarith only [h4, h9028, hlam]
                                                    · linarith only [h8937, h9028, hlam]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h0, h4, h8943, h8949, h8951, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9013_1]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8939, h8943, h8949, h8951, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9013_1]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8948, hlam, p9013_0]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [hlam, p9013_0]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8948, h8951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9013_1]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8937, hlam, p9013_0]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8946, hlam, p9013_0]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8949, hlam, p9013_0]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [h8951, hlam, p9013_0]
                                                  · have p9013_0 := h9013c.1
                                                    have p9013_1 := h9013c.2.1
                                                    have p9013_2 := h9013c.2.2.1
                                                    have p9013_3 := h9013c.2.2.2
                                                    linarith only [hlam, p9013_0]
                                              · linarith only [h9010, hlam, p8979_0]
                                            · linarith only [h4, h9009, hlam]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        rcases p8979_3 (m.d 0 2) (by simp) with h9043 | h9043
                                        · linarith only [h7337, h9043, hlam]
                                        · linarith only [h0, h9043, hlam]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h8948, hlam, p8979_1]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        rcases p8979_3 (m.d 0 2) (by simp) with h9048 | h9048
                                        · linarith only [h7337, h9048, hlam]
                                        · linarith only [h8360, h9048, hlam]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h8360, hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h8943, hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h8949, hlam, p8979_1]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [h8950, hlam, p8979_0]
                                      · have p8979_0 := h8979c.1
                                        have p8979_1 := h8979c.2.1
                                        have p8979_2 := h8979c.2.2.1
                                        have p8979_3 := h8979c.2.2.2
                                        linarith only [hlam, p8979_0]
                            · linarith only [h2, h8970, hlam]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            rcases p8952_3 (m.d 0 1) (by simp) with h9057 | h9057
                            · rcases p8952_3 (m.d 0 2) (by simp) with h9058 | h9058
                              · linarith only [h0, h9058, hlam]
                              · linarith only [h8360, h9058, hlam]
                            · linarith only [h3, h9057, hlam]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h0, hlam, p8952_0]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [hlam, p8952_0]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h4, hlam, p8952_0]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h7337, hlam, p8952_1]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h3, h4, h8361, h8943, h8948, h8949, h8951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8952_1]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h1, hlam, p8952_1]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h8361, h8948, hc02, hc23, hlam, hphi, p8952_1]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [hlam, p8952_0]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h8361, hlam, p8952_1]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h3, h8361, h8943, h8948, h8949, h8951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8952_1]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h2, hlam, p8952_0]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h0, h8361, h8943, h8948, h8949, h8951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8952_1]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h1, h8361, h8939, h8943, h8948, h8949, h8951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8952_1]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [hlam, p8952_0]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            rcases p8952_3 (m.d 0 1) (by simp) with h9076 | h9076
                            · rcases p8952_3 (m.d 0 2) (by simp) with h9077 | h9077
                              · linarith only [h7337, h9077, hlam]
                              · linarith only [h8360, h9077, hlam]
                            · linarith only [h3, h9076, hlam]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h3, hlam, p8952_0]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h8360, hlam, p8952_1]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h8937, hlam, p8952_0]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [h8938, hlam, p8952_1]
                          · have p8952_0 := h8952c.1
                            have p8952_1 := h8952c.2.1
                            have p8952_2 := h8952c.2.2.1
                            have p8952_3 := h8952c.2.2.2
                            linarith only [hlam, p8952_0]
                        · linarith only [h1, h8361, h8938, h8939, h8943, h8949, h8951, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h3, h7337, h8943, h8947, h8949, h8950, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h4, h8361, h8948, h8949, hc02, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9089 | h9089
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9090 | h9090
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9091 | h9091
                        · rcases h0bigk with h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c | h9092c
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [hlam, p9092_0]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            rcases p9092_3 (m.d 0 1) (by simp) with h9094 | h9094
                            · rcases p9092_3 (m.d 0 2) (by simp) with h9095 | h9095
                              · linarith only [h0, h9095, hlam]
                              · rcases p9092_3 (m.d 0 3) (by simp) with h9097 | h9097
                                · linarith only [h1, h9097, hlam]
                                · linarith only [h4, h9097, hlam]
                            · linarith only [h0, h9094, hlam]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            rcases p9092_3 (m.d 0 1) (by simp) with h9101 | h9101
                            · rcases p9092_3 (m.d 0 2) (by simp) with h9102 | h9102
                              · linarith only [h0, h9102, hlam]
                              · rcases p9092_3 (m.d 0 3) (by simp) with h9104 | h9104
                                · linarith only [h1, h9104, hlam]
                                · rcases p9092_3 (m.d 0 4) (by simp) with h9106 | h9106
                                  · linarith only [h2, h9106, hlam]
                                  · linarith only [h8361, h9106, hlam]
                            · linarith only [h1, h9101, hlam]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            rcases p9092_3 (m.d 0 1) (by simp) with h9110 | h9110
                            · rcases p9092_3 (m.d 0 2) (by simp) with h9111 | h9111
                              · linarith only [h0, h9111, hlam]
                              · rcases p9092_3 (m.d 0 3) (by simp) with h9113 | h9113
                                · linarith only [h1, h9113, hlam]
                                · rcases p9092_3 (m.d 0 4) (by simp) with h9115 | h9115
                                  · linarith only [h2, h9115, hlam]
                                  · rcases p9092_3 (m.d 0 5) (by simp) with h9117 | h9117
                                    · linarith only [h3, h9117, hlam]
                                    · rcases h2bigk with h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h4, h8943, h9089, h9091, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9119_1]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h4, hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h7337, hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h4, h8948, h9089, h9091, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9119_1]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h0, hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h8939, hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h8941, hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h0, h4, h8948, h9089, h9091, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9119_1]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h8948, hc02, hc34, hlam, hphi, ht23, p9119_1]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h8948, hc12, hc34, hlam, hphi, ht23, p9119_1]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h8948, hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        rcases p9119_3 (m.d 0 2) (by simp) with h9134 | h9134
                                        · linarith only [h4, h9134, hlam]
                                        · linarith only [h8360, h9134, hlam]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        rcases p9119_3 (m.d 0 2) (by simp) with h9137 | h9137
                                        · linarith only [h9137, hlam, p9119_0]
                                        · rcases p9119_3 (m.d 1 2) (by simp) with h9139 | h9139
                                          · linarith only [h8941, h9139, hlam]
                                          · rcases p9119_3 (m.d 2 3) (by simp) with h9141 | h9141
                                            · linarith only [h8948, h9141, hlam]
                                            · linarith only [h4, h9141, hlam]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        rcases p9119_3 (m.d 0 2) (by simp) with h9144 | h9144
                                        · linarith only [h7337, h9144, hlam]
                                        · linarith only [h0, h9144, hlam]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h4, h8948, hc02, hc34, hlam, hphi, ht23, p9119_1]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        rcases p9119_3 (m.d 0 2) (by simp) with h9149 | h9149
                                        · linarith only [h7337, h9149, hlam]
                                        · linarith only [h8360, h9149, hlam]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h8360, hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h8943, hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h9089, hlam, p9119_1]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [h9090, hlam, p9119_0]
                                      · have p9119_0 := h9119c.1
                                        have p9119_1 := h9119c.2.1
                                        have p9119_2 := h9119c.2.2.1
                                        have p9119_3 := h9119c.2.2.2
                                        linarith only [hlam, p9119_0]
                            · linarith only [h2, h9110, hlam]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            rcases p9092_3 (m.d 0 1) (by simp) with h9158 | h9158
                            · rcases p9092_3 (m.d 0 2) (by simp) with h9159 | h9159
                              · linarith only [h0, h9159, hlam]
                              · linarith only [h8360, h9159, hlam]
                            · linarith only [h3, h9158, hlam]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [h0, hlam, p9092_0]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [hlam, p9092_0]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [h4, hlam, p9092_0]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [h7337, hlam, p9092_1]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [h3, h4, h8943, h8948, h9089, h9091, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9092_1]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [h1, hlam, p9092_1]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [h8361, hc02, hc34, hlam, hphi, ht23, p9092_1]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [hlam, p9092_0]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [h8361, hlam, p9092_1]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            rcases p9092_3 (m.d 0 1) (by simp) with h9172 | h9172
                            · rcases p9092_3 (m.d 0 2) (by simp) with h9173 | h9173
                              · linarith only [h4, h9173, hlam]
                              · linarith only [h8360, h9173, hlam]
                            · linarith only [h3, h9172, hlam]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [h2, hlam, p9092_0]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            rcases p9092_3 (m.d 0 1) (by simp) with h9178 | h9178
                            · rcases p9092_3 (m.d 0 2) (by simp) with h9179 | h9179
                              · linarith only [h7337, h9179, hlam]
                              · rcases p9092_3 (m.d 0 3) (by simp) with h9181 | h9181
                                · linarith only [h8361, h9181, hlam]
                                · linarith only [h4, h9181, hlam]
                            · linarith only [h0, h9178, hlam]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            rcases p9092_3 (m.d 0 1) (by simp) with h9185 | h9185
                            · rcases p9092_3 (m.d 0 2) (by simp) with h9186 | h9186
                              · linarith only [h7337, h9186, hlam]
                              · rcases p9092_3 (m.d 0 3) (by simp) with h9188 | h9188
                                · linarith only [h8361, h9188, hlam]
                                · rcases p9092_3 (m.d 0 4) (by simp) with h9190 | h9190
                                  · rcases p9092_3 (m.d 0 5) (by simp) with h9191 | h9191
                                    · linarith only [h8938, h9191, hlam]
                                    · rcases h2bigk with h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c | h9193c
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h4, h8943, h8948, h9089, h9091, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9193_1]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h4, hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h7337, hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h4, h7337, h8948, h9089, h9091, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9092_1, p9193_1]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h0, hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h8939, hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h8941, hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h0, h4, h7337, h8948, h9089, h9091, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9092_1, p9193_1]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h8948, hc02, hc34, hlam, hphi, ht23, p9193_1]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h8948, hc12, hc34, hlam, hphi, ht23, p9193_1]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h8948, hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        rcases p9193_3 (m.d 0 2) (by simp) with h9208 | h9208
                                        · linarith only [h4, h9208, hlam]
                                        · linarith only [h8360, h9208, hlam]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        rcases p9193_3 (m.d 0 2) (by simp) with h9211 | h9211
                                        · linarith only [h9211, hlam, p9193_0]
                                        · rcases p9193_3 (m.d 1 2) (by simp) with h9213 | h9213
                                          · linarith only [h8941, h9213, hlam]
                                          · rcases p9193_3 (m.d 2 3) (by simp) with h9215 | h9215
                                            · linarith only [h8948, h9215, hlam]
                                            · linarith only [h4, h9215, hlam]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        rcases p9193_3 (m.d 0 2) (by simp) with h9218 | h9218
                                        · linarith only [h7337, h9218, hlam]
                                        · linarith only [h0, h9218, hlam]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h0, h4, h8943, h8948, h9089, h9091, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9193_1]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h0, h4, h7337, h8943, hlam, p9092_1, p9193_2]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h8360, hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h8943, hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h9089, hlam, p9193_1]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [h9090, hlam, p9193_0]
                                      · have p9193_0 := h9193c.1
                                        have p9193_1 := h9193c.2.1
                                        have p9193_2 := h9193c.2.2.1
                                        have p9193_3 := h9193c.2.2.2
                                        linarith only [hlam, p9193_0]
                                  · linarith only [h8361, h9190, hlam]
                            · linarith only [h1, h9185, hlam]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [hlam, p9092_0]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            rcases p9092_3 (m.d 0 1) (by simp) with h9232 | h9232
                            · rcases p9092_3 (m.d 0 2) (by simp) with h9233 | h9233
                              · linarith only [h7337, h9233, hlam]
                              · linarith only [h8360, h9233, hlam]
                            · linarith only [h3, h9232, hlam]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [h3, hlam, p9092_0]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [h8360, hlam, p9092_1]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [h8937, hlam, p9092_0]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [h8938, hlam, p9092_1]
                          · have p9092_0 := h9092c.1
                            have p9092_1 := h9092c.2.1
                            have p9092_2 := h9092c.2.2.1
                            have p9092_3 := h9092c.2.2.2
                            linarith only [hlam, p9092_0]
                        · linarith only [h8361, h8938, h9091, hlam]
                      · linarith only [h0, h3, h7337, h8943, h8947, h9089, h9090, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h4, h8937, h8943, h9089, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h8939, h8943, h8944, h8947, hlam]
              · linarith only [h8361, h8937, h8939, h8943, h8946, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
          · linarith only [h4, h8360, h8943, hc12, hc23, hlam, hphi]
    · linarith only [h4, h8360, h8361, h8938, hlam]
  · linarith only [h4, h8360, h8937, hlam]

set_option maxHeartbeats 9116000 in
set_option maxHeartbeats 9116000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s11_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h8360 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  rcases m.htr 0 3 4 (by decide) (by decide) with h8361 | h8361
  · exact r1l7_10_12_23_L_I_L_I_H_I_s11_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 h8360 h8361
  · exact r1l7_10_12_23_L_I_L_I_H_I_s11_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 h8360 h8361

set_option maxHeartbeats 9116000 in
set_option maxHeartbeats 9116000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s11_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  exact r1l7_10_12_23_L_I_L_I_H_I_s12 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h7337 h8360

set_option maxHeartbeats 9116000 in
set_option maxHeartbeats 9116000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s11 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  rcases m.htr 0 2 5 (by decide) (by decide) with h8360 | h8360
  · exact r1l7_10_12_23_L_I_L_I_H_I_s11_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 h8360
  · exact r1l7_10_12_23_L_I_L_I_H_I_s11_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 h8360

end R2N4
