import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_20S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5035 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 0 2 5 (by decide) (by decide) with h6939 | h6939
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6940 | h6940
    · linarith only [h5034, h5035, h6940, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6942 | h6942
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6943 | h6943
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6944 | h6944
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6945 | h6945
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6946 | h6946
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6947 | h6947
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6948 | h6948
                  · linarith only [h5034, h5035, h6940, h6944, h6948, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6950 | h6950
                    · linarith only [h5034, h5035, h6943, h6946, h6948, h6950, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6952 | h6952
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6953 | h6953
                        · rcases h2bigk with h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c | h6954c
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h0, hlam, p6954_1]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h5035, h6943, h6946, h6948, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6954_1]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h5035, hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h5035, h6943, h6946, h6948, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6954_1]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p6954_1]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            rcases p6954_3 (m.d 0 2) (by simp) with h6962 | h6962
                            · linarith only [h0, h6962, hlam]
                            · linarith only [h5034, h6962, hlam]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h5035, h6939, h6950, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6954_1]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            rcases p6954_3 (m.d 0 2) (by simp) with h6966 | h6966
                            · linarith only [h0, h6966, hlam]
                            · linarith only [h6939, h6966, hlam]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h5034, hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h6943, hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h6948, hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h6950, hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h6939, h6950, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p6954_1]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h6944, hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h6943, h6946, h6948, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6954_1]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h6943, h6946, h6948, h6950, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6954_1]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h6939, hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h6945, hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h6939, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6954_1]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [h6952, hlam, p6954_0]
                          · have p6954_0 := h6954c.1
                            have p6954_1 := h6954c.2.1
                            have p6954_2 := h6954c.2.2.1
                            have p6954_3 := h6954c.2.2.2
                            linarith only [hlam, p6954_0]
                        · linarith only [h5034, h5035, h6948, h6953, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h5035, h6939, h6942, h6952, hlam]
                · linarith only [h3667, h5035, h6939, h6942, h6947, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6987 | h6987
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6988 | h6988
                  · linarith only [h5034, h5035, h6944, h6946, h6988, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6990 | h6990
                    · linarith only [h5034, h5035, h6944, h6990, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6992 | h6992
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6993 | h6993
                        · rcases h2bigk with h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c | h6994c
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h0, hlam, p6994_1]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h5035, h6944, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6994_1]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h5035, hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h5035, h6944, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6994_1]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p6994_1]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            rcases p6994_3 (m.d 0 2) (by simp) with h7002 | h7002
                            · linarith only [h0, h7002, hlam]
                            · linarith only [h5034, h7002, hlam]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h3667, h5035, hc01, hc12, hlam, hphi, p6994_1]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            rcases p6994_3 (m.d 0 2) (by simp) with h7006 | h7006
                            · linarith only [h0, h7006, hlam]
                            · linarith only [h6939, h7006, hlam]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h5034, hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h6943, hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h6988, hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h6990, hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h6939, h6944, h6990, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6994_1]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h6944, hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h6944, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6994_1]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h6944, h6990, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6994_1]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h6939, hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h6945, hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h6939, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6994_1]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [h6992, hlam, p6994_0]
                          · have p6994_0 := h6994c.1
                            have p6994_1 := h6994c.2.1
                            have p6994_2 := h6994c.2.2.1
                            have p6994_3 := h6994c.2.2.2
                            linarith only [hlam, p6994_0]
                        · linarith only [h3667, h6942, h6946, h6993, hlam]
                      · linarith only [h5035, h6939, h6942, h6992, hlam]
                · linarith only [h5035, h6939, h6942, h6944, h6987, hlam]
            · linarith only [h5035, h6939, h6944, h6945, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7028 | h7028
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7029 | h7029
              · linarith only [h6943, h6944, h7029, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7031 | h7031
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7032 | h7032
                  · linarith only [h0, h5034, h6944, h7029, h7032, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7034 | h7034
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7035 | h7035
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7036 | h7036
                        · rcases h2bigk with h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [hlam, p7037_0]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h0, hlam, p7037_1]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h7034, h7036, hc02, hc45, hlam, hphi, ht0b, ht5b, p7037_1]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h5035, hlam, p7037_0]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h0, h6944, h7032, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7037_1]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h6944, h7032, hc02, hc34, hlam, hphi, ht23, p7037_1]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [hlam, p7037_0]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h6944, h7032, h7034, h7036, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7037_1]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h6944, hlam, p7037_0]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h6944, h7032, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7037_1]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h5034, hlam, p7037_0]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h6943, hlam, p7037_0]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [hlam, p7037_0]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h7032, hlam, p7037_0]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h5034, hc02, hc25, hlam, hphi, ht0b, ht5b, p7037_1]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h7032, hc02, hc34, hlam, hphi, ht23, p7037_1]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h7032, hc12, hc34, hlam, hphi, ht23, p7037_1]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h7032, hc23, hc34, hlam, hphi, p7037_1]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [hlam, p7037_0]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            rcases p7037_3 (m.d 0 2) (by simp) with h7057 | h7057
                            · linarith only [h5035, h7057, hlam]
                            · linarith only [h6939, h7057, hlam]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h6939, hlam, p7037_0]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h7028, hlam, p7037_0]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h7034, hlam, p7037_1]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [h7035, hlam, p7037_0]
                          · have p7037_0 := h7037c.1
                            have p7037_1 := h7037c.2.1
                            have p7037_2 := h7037c.2.2.1
                            have p7037_3 := h7037c.2.2.2
                            linarith only [hlam, p7037_0]
                        · linarith only [h5034, h5035, h7032, h7036, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h6942, h6944, h7035, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7067 | h7067
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7068 | h7068
                        · rcases h2bigk with h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c | h7069c
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h0, hlam, p7069_1]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h5035, h7032, hc23, hc34, hlam, hphi, p7069_1]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h5035, hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h5035, h7032, h7034, hc23, hc34, hlam, hphi, p7069_1]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7069_1]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h6944, h7032, hc23, hc34, hlam, hphi, p7069_1]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h6944, hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h6944, h7032, h7034, hc23, hc34, hlam, hphi, p7069_1]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h5034, hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h6943, hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h7032, hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h7034, hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h6939, h7032, h7034, hc23, hc34, hlam, hphi, p7069_1]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h7032, hc12, hc34, hlam, hphi, ht23, p7069_1]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h7032, hc23, hc34, hlam, hphi, p7069_1]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h7032, h7034, hc23, hc34, hlam, hphi, p7069_1]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h6939, hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h7028, hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h6939, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7069_1]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [h7067, hlam, p7069_0]
                          · have p7069_0 := h7069c.1
                            have p7069_1 := h7069c.2.1
                            have p7069_2 := h7069c.2.2.1
                            have p7069_3 := h7069c.2.2.2
                            linarith only [hlam, p7069_0]
                        · linarith only [h0, h6939, h6944, h7032, h7067, h7068, hlam]
                      · linarith only [h0, h6944, h7067, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h3667, h6942, h7031, hlam]
            · linarith only [h0, h6939, h7028, hlam]
        · linarith only [h0, h5034, h6943, hlam]
      · linarith only [h5035, h6939, h6942, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h7101 | h7101
    · linarith only [h5034, h5035, h7101, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h7103 | h7103
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7104 | h7104
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7105 | h7105
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7106 | h7106
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7107 | h7107
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7108 | h7108
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7109 | h7109
                  · linarith only [h5034, h5035, h7101, h7105, h7109, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7111 | h7111
                    · linarith only [h5034, h5035, h7104, h7107, h7109, h7111, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7113 | h7113
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7114 | h7114
                        · rcases h2bigk with h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c | h7115c
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h0, hlam, p7115_1]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h6939, h7104, h7107, h7109, h7113, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7115_1]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h5035, hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h6939, hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7115_1]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            rcases p7115_3 (m.d 0 2) (by simp) with h7123 | h7123
                            · linarith only [h0, h7123, hlam]
                            · linarith only [h5034, h7123, hlam]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h5034, h5035, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7115_1]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h5034, h6939, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7115_1]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h5034, hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h7104, hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h7109, hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h7111, hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h5034, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p7115_1]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h7105, hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h7104, h7107, h7109, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7115_1]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h5034, h6939, h7104, h7107, h7109, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7115_1]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h5034, h7106, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7115_1]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h7106, hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h7106, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7115_1]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [h7113, hlam, p7115_0]
                          · have p7115_0 := h7115c.1
                            have p7115_1 := h7115c.2.1
                            have p7115_2 := h7115c.2.2.1
                            have p7115_3 := h7115c.2.2.2
                            linarith only [hlam, p7115_0]
                        · linarith only [h3667, h5034, h5035, h7103, h7109, h7114, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h5035, h7103, h7113, hlam]
                · linarith only [h3667, h5035, h7103, h7108, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7146 | h7146
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7147 | h7147
                  · linarith only [h5034, h5035, h7105, h7107, h7147, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7149 | h7149
                    · linarith only [h5034, h5035, h7105, h7149, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7151 | h7151
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7152 | h7152
                        · rcases h2bigk with h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c | h7153c
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h0, hlam, p7153_1]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h6939, h7105, h7151, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7153_1]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h5035, hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h6939, hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7153_1]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            rcases p7153_3 (m.d 0 2) (by simp) with h7161 | h7161
                            · linarith only [h0, h7161, hlam]
                            · linarith only [h5034, h7161, hlam]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h5035, h7103, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7153_1]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h5034, h6939, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7153_1]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h5034, hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h7104, hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h7147, hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h7149, hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h5034, h7105, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7153_1]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h7105, hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h7105, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7153_1]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h5034, h6939, h7105, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7153_1]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h5034, h7106, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7153_1]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h7106, hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h7106, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7153_1]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [h7151, hlam, p7153_0]
                          · have p7153_0 := h7153c.1
                            have p7153_1 := h7153c.2.1
                            have p7153_2 := h7153c.2.2.1
                            have p7153_3 := h7153c.2.2.2
                            linarith only [hlam, p7153_0]
                        · linarith only [h3667, h7103, h7107, h7152, hlam]
                      · linarith only [h5035, h7103, h7151, hlam]
                · linarith only [h3667, h5035, h7103, h7146, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h5035, h7105, h7106, hc02, hc25, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7185 | h7185
            · linarith only [h5034, h6939, h7105, h7185, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7187 | h7187
              · linarith only [h7104, h7105, h7187, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7189 | h7189
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7190 | h7190
                  · linarith only [h0, h5034, h7105, h7187, h7190, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7192 | h7192
                    · linarith only [h0, h5034, h7185, h7192, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7194 | h7194
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7195 | h7195
                        · rcases h2bigk with h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c | h7196c
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h0, hlam, p7196_1]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h0, h7185, h7190, h7194, hc23, hc34, hlam, hphi, p7196_1]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h5035, hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h6939, hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h7185, h7190, h7194, hc02, hc34, hlam, hphi, ht23, p7196_1]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h7185, h7190, h7194, hc23, hc34, hlam, hphi, p7196_1]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h7105, hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h7185, hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h5034, hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h7104, hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h7190, hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h7192, hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h5034, h7190, hc23, hc34, hlam, hphi, p7196_1]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h7190, hc12, hc34, hlam, hphi, ht23, p7196_1]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h7190, hc23, hc34, hlam, hphi, p7196_1]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h5034, h6939, h7190, hc23, hc34, hlam, hphi, p7196_1]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h5034, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p7196_1]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h0, h7192, hc01, hc35, hlam, hphi, ht12, ht23, p7196_1]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h7192, hc23, hc35, hlam, hphi, p7196_1]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [h7194, hlam, p7196_0]
                          · have p7196_0 := h7196c.1
                            have p7196_1 := h7196c.2.1
                            have p7196_2 := h7196c.2.2.1
                            have p7196_3 := h7196c.2.2.2
                            linarith only [hlam, p7196_0]
                        · linarith only [h3667, h5034, h5035, h7103, h7190, h7195, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3667, h7103, h7105, h7194, hlam]
                · linarith only [h3667, h7103, h7189, hlam]
        · linarith only [h0, h5034, h7104, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7226 | h7226
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7227 | h7227
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7228 | h7228
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7229 | h7229
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7230 | h7230
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7231 | h7231
                  · linarith only [h5034, h5035, h7103, h7226, h7229, h7230, h7231, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7233 | h7233
                    · linarith only [h5034, h5035, h7103, h7226, h7229, h7230, h7233, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7235 | h7235
                      · linarith only [h5034, h5035, h7103, h7231, h7235, hc23, hc34, hlam, hphi]
                      · linarith only [h5034, h5035, h7226, h7229, h7230, h7235, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h5034, h5035, h7227, h7230, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7239 | h7239
                · linarith only [h5034, h5035, h7103, h7229, h7239, hc23, hc34, hlam, hphi]
                · linarith only [h5034, h5035, h7227, h7239, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h5034, h5035, h7227, h7228, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7243 | h7243
            · linarith only [h5034, h6939, h7227, h7243, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7245 | h7245
              · linarith only [h7226, h7227, h7245, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7247 | h7247
                · linarith only [h5034, h5035, h7103, h7245, h7247, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7249 | h7249
                  · linarith only [h0, h5034, h7227, h7247, h7249, hc34, hc45, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7251 | h7251
                    · linarith only [h0, h5034, h7243, h7251, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7253 | h7253
                      · linarith only [h3667, h7247, h7249, h7253, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h5034, h5035, h7253, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h0, h5034, h5035, h7226, hc01, hc24, hlam, hphi, ht12]

set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 0 2 4 (by decide) (by decide) with h5035 | h5035
  · exact r1l7_22_14_H_I_L_I_s3_x0_x0 m hb2 hb4 hg0 hg3667 h5034 h5035
  · exact r1l7_22_14_H_I_L_I_s3_x0_x1 m hb2 hb4 hg0 hg3667 h5034 h5035

set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7257 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 0 2 5 (by decide) (by decide) with h7258 | h7258
  · rcases m.htr 0 3 4 (by decide) (by decide) with h7259 | h7259
    · rcases m.htr 0 4 5 (by decide) (by decide) with h7260 | h7260
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7261 | h7261
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7262 | h7262
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7263 | h7263
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7264 | h7264
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7265 | h7265
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7266 | h7266
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7267 | h7267
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7268 | h7268
                      · linarith only [h5034, h7257, h7261, h7268, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h5034, h7257, h7260, h7261, h7268, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h5034, h7258, h7267, hlam]
                  · linarith only [h5034, h7259, h7266, hlam]
                · linarith only [h3667, h5034, h7257, h7260, h7261, h7265, hc01, hc13, hlam, hphi]
              · linarith only [h5034, h7257, h7259, h7261, h7264, hlam]
            · linarith only [h5034, h7258, h7261, h7263, hlam]
          · linarith only [h5034, h7261, h7262, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7277 | h7277
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7278 | h7278
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7279 | h7279
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7280 | h7280
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7281 | h7281
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7282 | h7282
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7283 | h7283
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7284 | h7284
                        · rcases h2bigk with h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [hlam, p7285_0]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h0, hlam, p7285_1]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h5034, hlam, p7285_0]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h0, h7261, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7285_1]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h0, h7261, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p7285_1]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7261, hc02, hc23, hlam, hphi, p7285_1]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [hlam, p7285_0]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7261, hlam, p7285_0]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7261, h7281, h7284, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7285_1]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7261, h7282, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p7285_1]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7257, h7281, h7284, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7285_1]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p7285_1]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [hlam, p7285_0]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7281, h7284, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7285_1]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            rcases p7285_3 (m.d 0 2) (by simp) with h7300 | h7300
                            · linarith only [h5034, h7300, hlam]
                            · linarith only [h7258, h7300, hlam]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7257, hlam, p7285_0]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7277, hlam, p7285_0]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7281, hlam, p7285_1]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [hlam, p7285_0]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7257, h7282, h7284, hc02, hc45, hlam, hphi, ht0b, ht5b, p7285_1]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7258, hlam, p7285_0]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7278, hlam, p7285_0]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7282, hlam, p7285_1]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [h7283, hlam, p7285_0]
                          · have p7285_0 := h7285c.1
                            have p7285_1 := h7285c.2.1
                            have p7285_2 := h7285c.2.2.1
                            have p7285_3 := h7285c.2.2.2
                            linarith only [hlam, p7285_0]
                        · linarith only [h0, h7257, h7261, h7283, h7284, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7314 | h7314
                        · linarith only [h7281, h7283, h7314, hlam]
                        · rcases h2bigk with h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c | h7316c
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [hlam, p7316_0]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h0, hlam, p7316_1]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h5034, hlam, p7316_0]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h0, h7261, h7281, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7316_1]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h0, h7261, h7281, h7283, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7316_1]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7261, hc02, hc23, hlam, hphi, p7316_1]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [hlam, p7316_0]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7261, hlam, p7316_0]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7261, h7281, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7316_1]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7261, h7281, h7283, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7316_1]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7257, h7260, h7281, h7283, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7316_1]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p7316_1]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [hlam, p7316_0]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            rcases p7316_3 (m.d 0 2) (by simp) with h7330 | h7330
                            · linarith only [h5034, h7330, hlam]
                            · linarith only [h7257, h7330, hlam]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            rcases p7316_3 (m.d 0 2) (by simp) with h7333 | h7333
                            · linarith only [h5034, h7333, hlam]
                            · linarith only [h7258, h7333, hlam]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7257, hlam, p7316_0]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7277, hlam, p7316_0]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7281, hlam, p7316_1]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [hlam, p7316_0]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7283, hlam, p7316_1]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7258, hlam, p7316_0]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7278, hlam, p7316_0]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7282, hlam, p7316_1]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [h7258, h7281, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7316_1]
                          · have p7316_0 := h7316c.1
                            have p7316_1 := h7316c.2.1
                            have p7316_2 := h7316c.2.2.1
                            have p7316_3 := h7316c.2.2.2
                            linarith only [hlam, p7316_0]
                    · linarith only [h0, h7261, h7282, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h3667, h7261, h7277, h7281, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h3667, h7257, h7260, h7280, hc01, hc12, hlam, hphi]
              · linarith only [h0, h7257, h7259, h7261, h7279, hlam]
            · linarith only [h0, h7258, h7278, hlam]
          · linarith only [h0, h7257, h7277, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7352 | h7352
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7353 | h7353
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7354 | h7354
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7355 | h7355
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7356 | h7356
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7357 | h7357
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7358 | h7358
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7359 | h7359
                      · linarith only [h0, h3667, h7257, h7260, h7359, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7361 | h7361
                        · linarith only [h3667, h5034, h7259, h7260, h7352, h7361, hc01, hc12, hlam, hphi]
                        · rcases h2bigk with h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c | h7363c
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [hlam, p7363_0]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h0, hlam, p7363_1]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h5034, hlam, p7363_0]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h5034, h7352, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7363_1]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h5034, h7352, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p7363_1]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7363_1]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [hlam, p7363_0]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h0, h5034, hc01, hc12, hlam, hphi, p7363_1]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            rcases p7363_3 (m.d 0 2) (by simp) with h7372 | h7372
                            · linarith only [h0, h7372, hlam]
                            · linarith only [h7257, h7372, hlam]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            rcases p7363_3 (m.d 0 2) (by simp) with h7375 | h7375
                            · linarith only [h0, h7375, hlam]
                            · linarith only [h7258, h7375, hlam]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h7258, h7357, h7359, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7363_1]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h7352, hlam, p7363_0]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [hlam, p7363_0]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h7352, h7357, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7363_1]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h7352, h7357, h7359, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7363_1]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h7257, hlam, p7363_0]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h7353, hlam, p7363_0]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h7357, hlam, p7363_1]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [hlam, p7363_0]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h7359, hlam, p7363_1]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h7258, hlam, p7363_0]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h7354, hlam, p7363_0]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h7358, hlam, p7363_1]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [h7258, h7357, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7363_1]
                          · have p7363_0 := h7363c.1
                            have p7363_1 := h7363c.2.1
                            have p7363_2 := h7363c.2.2.1
                            have p7363_3 := h7363c.2.2.2
                            linarith only [hlam, p7363_0]
                    · linarith only [h5034, h7258, h7358, hlam]
                  · linarith only [h5034, h7259, h7357, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7395 | h7395
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7396 | h7396
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7397 | h7397
                      · linarith only [h5034, h7257, h7352, h7356, h7397, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7399 | h7399
                        · linarith only [h3667, h5034, h7258, h7352, h7356, h7395, h7397, h7399, hc01, hc12, hlam, hphi]
                        · rcases h2bigk with h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c | h7401c
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [hlam, p7401_0]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h0, hlam, p7401_1]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h5034, hlam, p7401_0]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h5034, h7352, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7401_1]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h5034, h7352, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p7401_1]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7401_1]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [hlam, p7401_0]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h0, h5034, hc01, hc12, hlam, hphi, p7401_1]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            rcases p7401_3 (m.d 0 2) (by simp) with h7410 | h7410
                            · linarith only [h0, h7410, hlam]
                            · linarith only [h7257, h7410, hlam]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            rcases p7401_3 (m.d 0 2) (by simp) with h7413 | h7413
                            · linarith only [h0, h7413, hlam]
                            · linarith only [h7258, h7413, hlam]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h7258, h7395, h7397, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7401_1]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h7352, hlam, p7401_0]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [hlam, p7401_0]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h7352, h7395, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7401_1]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h7352, h7395, h7397, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7401_1]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h7257, hlam, p7401_0]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h7353, hlam, p7401_0]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h7395, hlam, p7401_1]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [hlam, p7401_0]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h7397, hlam, p7401_1]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h7258, hlam, p7401_0]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h7354, hlam, p7401_0]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h7396, hlam, p7401_1]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [h7258, h7395, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7401_1]
                          · have p7401_0 := h7401c.1
                            have p7401_1 := h7401c.2.1
                            have p7401_2 := h7401c.2.2.1
                            have p7401_3 := h7401c.2.2.2
                            linarith only [hlam, p7401_0]
                    · linarith only [h5034, h7258, h7396, hlam]
                  · linarith only [h5034, h7259, h7395, hlam]
              · linarith only [h5034, h7257, h7259, h7352, h7355, hlam]
            · linarith only [h5034, h7258, h7354, hc12, hc23, hlam, hphi]
          · linarith only [h5034, h7352, h7353, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7436 | h7436
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7437 | h7437
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7438 | h7438
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7439 | h7439
                · linarith only [h3667, h7260, h7352, h7436, h7439, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7441 | h7441
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7442 | h7442
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7443 | h7443
                      · linarith only [h0, h7257, h7352, h7439, h7443, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7445 | h7445
                        · linarith only [h3667, h7439, h7445, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h2bigk with h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c | h7447c
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [hlam, p7447_0]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h0, hlam, p7447_1]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h5034, hlam, p7447_0]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h0, h7352, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7447_1]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h0, h7352, h7441, h7443, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7447_1]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7352, hc02, hc23, hlam, hphi, p7447_1]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [hlam, p7447_0]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7352, hlam, p7447_0]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7352, h7441, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7447_1]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7352, h7441, h7443, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7447_1]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7258, h7441, h7443, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7447_1]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p7447_1]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [hlam, p7447_0]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            rcases p7447_3 (m.d 0 2) (by simp) with h7461 | h7461
                            · linarith only [h5034, h7461, hlam]
                            · linarith only [h7257, h7461, hlam]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            rcases p7447_3 (m.d 0 2) (by simp) with h7464 | h7464
                            · linarith only [h5034, h7464, hlam]
                            · linarith only [h7258, h7464, hlam]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7257, hlam, p7447_0]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7436, hlam, p7447_0]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7441, hlam, p7447_1]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [hlam, p7447_0]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7443, hlam, p7447_1]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7258, hlam, p7447_0]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7437, hlam, p7447_0]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7442, hlam, p7447_1]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [h7258, h7441, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7447_1]
                          · have p7447_0 := h7447c.1
                            have p7447_1 := h7447c.2.1
                            have p7447_2 := h7447c.2.2.1
                            have p7447_3 := h7447c.2.2.2
                            linarith only [hlam, p7447_0]
                    · linarith only [h0, h7352, h7442, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h3667, h7352, h7437, h7439, h7441, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h7257, h7259, h7352, h7438, hlam]
            · linarith only [h0, h7258, h7437, hlam]
          · linarith only [h0, h7257, h7436, hlam]
    · linarith only [h5034, h7257, h7259, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h7483 | h7483
    · rcases m.htr 0 4 5 (by decide) (by decide) with h7484 | h7484
      · linarith only [h7257, h7258, h7484, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7486 | h7486
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7487 | h7487
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7488 | h7488
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7489 | h7489
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7490 | h7490
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7491 | h7491
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7492 | h7492
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7493 | h7493
                      · linarith only [h7257, h7258, h7484, h7488, h7493, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7495 | h7495
                        · linarith only [h7257, h7258, h7491, h7493, h7495, hlam]
                        · rcases h2bigk with h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [hlam, p7497_0]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h0, hlam, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h5034, hlam, p7497_0]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7258, h7486, h7489, h7490, h7493, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7258, hlam, p7497_0]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [hlam, p7497_0]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7492, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            rcases p7497_3 (m.d 0 2) (by simp) with h7506 | h7506
                            · linarith only [h0, h7506, hlam]
                            · linarith only [h7257, h7506, hlam]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7257, h7258, h7491, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7257, h7491, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7486, hlam, p7497_0]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [hlam, p7497_0]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7486, h7491, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7257, h7258, h7486, h7491, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7257, hlam, p7497_0]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7487, hlam, p7497_0]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7491, hlam, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [hlam, p7497_0]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7493, hlam, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7257, h7491, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7488, hlam, p7497_0]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7492, hlam, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [h7486, h7489, h7490, h7491, h7493, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                          · have p7497_0 := h7497c.1
                            have p7497_1 := h7497c.2.1
                            have p7497_2 := h7497c.2.2.1
                            have p7497_3 := h7497c.2.2.2
                            linarith only [hlam, p7497_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7525 | h7525
                      · linarith only [h5034, h7257, h7492, h7525, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7527 | h7527
                        · linarith only [h5034, h7257, h7483, h7492, h7525, h7527, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h5034, h7257, h7486, h7489, h7490, h7491, h7492, h7527, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h5034, h7483, h7491, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7531 | h7531
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7532 | h7532
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7533 | h7533
                      · linarith only [h3667, h7257, h7490, h7533, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7535 | h7535
                        · linarith only [h5034, h7257, h7258, h7483, h7486, h7488, h7490, h7535, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h2bigk with h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c | h7537c
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [hlam, p7537_0]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h0, hlam, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h5034, hlam, p7537_0]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7258, h7488, h7531, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7258, hlam, p7537_0]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [hlam, p7537_0]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7532, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            rcases p7537_3 (m.d 0 2) (by simp) with h7546 | h7546
                            · linarith only [h0, h7546, hlam]
                            · linarith only [h7257, h7546, hlam]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7257, h7258, h7531, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7257, h7531, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7486, hlam, p7537_0]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [hlam, p7537_0]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7486, h7531, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7257, h7258, h7486, h7531, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7257, hlam, p7537_0]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7487, hlam, p7537_0]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7531, hlam, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [hlam, p7537_0]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7533, hlam, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7257, h7531, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7488, hlam, p7537_0]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7532, hlam, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [h7488, h7490, h7531, hc34, hc45, hlam, hphi, p7537_1]
                          · have p7537_0 := h7537c.1
                            have p7537_1 := h7537c.2.1
                            have p7537_2 := h7537c.2.2.1
                            have p7537_3 := h7537c.2.2.2
                            linarith only [hlam, p7537_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7565 | h7565
                      · linarith only [h5034, h7257, h7490, h7532, h7565, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7567 | h7567
                        · linarith only [h5034, h7258, h7483, h7488, h7490, h7532, h7567, hc02, hc35, hlam, hphi, ht23]
                        · linarith only [h5034, h7257, h7531, h7532, h7567, hc34, hc45, hlam, hphi]
                  · linarith only [h5034, h7483, h7531, hlam]
              · linarith only [h5034, h7257, h7483, h7486, h7489, hlam]
            · linarith only [h5034, h7486, h7488, hc02, hc25, hlam, hphi]
          · linarith only [h5034, h7257, h7486, h7487, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7574 | h7574
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7575 | h7575
            · linarith only [h7257, h7258, h7486, h7575, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7577 | h7577
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7578 | h7578
                · linarith only [h3667, h7484, h7486, h7574, h7578, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7580 | h7580
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7581 | h7581
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7582 | h7582
                      · linarith only [h3667, h7257, h7578, h7582, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7584 | h7584
                        · linarith only [h0, h7575, h7582, h7584, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h2bigk with h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c | h7586c
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [hlam, p7586_0]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h0, hlam, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h5034, hlam, p7586_0]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h0, h7575, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7258, hlam, p7586_0]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7575, hc02, hc25, hlam, hphi, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [hlam, p7586_0]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7486, hlam, p7586_0]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7575, h7580, h7582, hc34, hc45, hlam, hphi, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7575, hlam, p7586_0]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7257, h7580, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [hlam, p7586_0]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            rcases p7586_3 (m.d 0 2) (by simp) with h7600 | h7600
                            · linarith only [h5034, h7600, hlam]
                            · linarith only [h7257, h7600, hlam]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7257, h7258, h7580, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7257, hlam, p7586_0]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7574, hlam, p7586_0]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7580, hlam, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [hlam, p7586_0]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7582, hlam, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7257, h7580, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h3667, h7574, hc01, hc25, hlam, hphi, ht12, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7581, hlam, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [h7580, h7582, hc34, hc45, hlam, hphi, p7586_1]
                          · have p7586_0 := h7586c.1
                            have p7586_1 := h7586c.2.1
                            have p7586_2 := h7586c.2.2.1
                            have p7586_3 := h7586c.2.2.2
                            linarith only [hlam, p7586_0]
                    · linarith only [h3667, h7486, h7574, h7581, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h3667, h7486, h7574, h7580, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h3667, h7483, h7486, h7574, h7577, hlam]
          · linarith only [h0, h7257, h7574, hlam]
    · linarith only [h5034, h7257, h7483, hlam]

end R2N4
