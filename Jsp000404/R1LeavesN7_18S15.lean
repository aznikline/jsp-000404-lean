import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_18S10
import Jsp000404.R1LeavesN7_18S13
import Jsp000404.R1LeavesN7_18S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8272 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h9441 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h9778 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 3 4 (by decide) (by decide) with h9991 | h9991
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9992 | h9992
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9993 | h9993
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9994 | h9994
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9995 | h9995
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9996 | h9996
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9997 | h9997
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9998 | h9998
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9999 | h9999
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10000 | h10000
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10001 | h10001
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10002 | h10002
                        · rcases h0bigk with h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [hlam, p10003_0]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h0, hlam, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h5743, hlam, p10003_0]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h6852, hlam, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h7594, hlam, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h10001, h9778, h9994, h9999, hc01, hc12, hlam, hphi, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [hlam, p10003_0]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h8272, hlam, p10003_0]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h9441, hlam, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h9778, hlam, p10003_0]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h5743, hc01, hc13, hlam, hphi, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h8272, h9994, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [hlam, p10003_0]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h8272, h9994, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h0, h8272, h9778, h9994, hc01, hc12, hlam, hphi, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h6852, hc01, hc14, hlam, hphi, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h0, h9441, h9994, h9999, hc01, hc12, hlam, hphi, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h9991, hlam, p10003_0]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [hlam, p10003_0]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h0, h9441, h9778, h9994, h9999, hc01, hc12, hlam, hphi, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h7594, hc01, hc15, hlam, hphi, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h0, h10001, h9778, h9994, h9999, hc01, hc12, hlam, hphi, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h9992, hlam, p10003_0]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [h9993, hlam, p10003_1]
                          · have p10003_0 := h10003c.1
                            have p10003_1 := h10003c.2.1
                            have p10003_2 := h10003c.2.2.1
                            have p10003_3 := h10003c.2.2.2
                            linarith only [hlam, p10003_0]
                        · rcases h0bigk with h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [hlam, p10029_0]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h0, hlam, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h5743, hlam, p10029_0]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h6852, hlam, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h7594, hlam, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [hlam, p10029_0]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h8272, hlam, p10029_0]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h9441, hlam, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h9778, hlam, p10029_0]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h8272, h9994, hc01, hc12, hlam, hphi, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h8272, h9994, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [hlam, p10029_0]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h8272, h9994, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h8272, h9994, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h6852, h9994, h9997, hc01, hc12, hlam, hphi, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h0, h9441, h9994, h9999, hc01, hc12, hlam, hphi, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h9991, hlam, p10029_0]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [hlam, p10029_0]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h0, h9441, h9778, h9994, h9999, hc01, hc12, hlam, hphi, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h7594, h9994, h9998, hc01, hc12, hlam, hphi, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h0, h10001, h9778, h9994, h9999, hc01, hc12, hlam, hphi, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h9992, hlam, p10029_0]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [h9993, hlam, p10029_1]
                          · have p10029_0 := h10029c.1
                            have p10029_1 := h10029c.2.1
                            have p10029_2 := h10029c.2.2.1
                            have p10029_3 := h10029c.2.2.2
                            linarith only [hlam, p10029_0]
                      · linarith only [h10001, h9441, h9993, hlam]
                    · linarith only [h10000, h8272, h9992, hlam]
                  · linarith only [h0, h5743, h8272, h9991, h9994, h9999, hc01, hc12, hlam, hphi]
                · linarith only [h5743, h9992, h9998, hlam]
              · linarith only [h8272, h9991, h9994, h9997, hlam]
            · linarith only [h0, h8272, h9994, h9996, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h8272, h9994, h9995, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10062 | h10062
          · linarith only [h0, h10062, h9441, h9994, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10064 | h10064
            · linarith only [h0, h10064, h9778, h9994, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10066 | h10066
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10067 | h10067
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10068 | h10068
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10069 | h10069
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10070 | h10070
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10071 | h10071
                        · rcases h0bigk with h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [hlam, p10072_0]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h0, hlam, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h5743, hlam, p10072_0]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h6852, hlam, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h7594, hlam, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h0, h10064, h10068, h10070, hc01, hc23, hlam, hphi, ht12, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [hlam, p10072_0]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h8272, hlam, p10072_0]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h9441, hlam, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h9778, hlam, p10072_0]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h5743, hc01, hc13, hlam, hphi, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h8272, hc02, hc23, hlam, hphi, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [hlam, p10072_0]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h6852, h8272, hc01, hc23, hlam, hphi, ht12, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h0, h8272, h9778, hc01, hc23, hlam, hphi, ht12, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h6852, hc01, hc14, hlam, hphi, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h0, h10068, h9441, hc01, hc23, hlam, hphi, ht12, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h9991, hlam, p10072_0]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [hlam, p10072_0]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h0, h10068, h9441, h9778, hc01, hc23, hlam, hphi, ht12, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h10067, h7594, hc01, hc13, hlam, hphi, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h0, h10068, h10070, h9778, hc01, hc23, hlam, hphi, ht12, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h9992, hlam, p10072_0]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [h9993, hlam, p10072_1]
                          · have p10072_0 := h10072c.1
                            have p10072_1 := h10072c.2.1
                            have p10072_2 := h10072c.2.2.1
                            have p10072_3 := h10072c.2.2.2
                            linarith only [hlam, p10072_0]
                        · rcases h0bigk with h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [hlam, p10098_0]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h0, hlam, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h5743, hlam, p10098_0]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h6852, hlam, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h7594, hlam, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h0, h10064, h10068, h10070, hc01, hc23, hlam, hphi, ht12, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [hlam, p10098_0]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h8272, hlam, p10098_0]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h9441, hlam, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h9778, hlam, p10098_0]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h5743, h9994, hc01, hc23, hlam, hphi, ht12, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h5743, h9994, hc02, hc23, hlam, hphi, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [hlam, p10098_0]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h10071, h5743, h9993, h9994, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h5743, h7594, h9994, hc01, hc23, hlam, hphi, ht12, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h10062, h10068, h6852, hc01, hc23, hlam, hphi, ht12, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h0, h10062, h10068, h6852, hc01, hc23, hlam, hphi, ht12, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h9991, hlam, p10098_0]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [hlam, p10098_0]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h0, h10062, h10068, h6852, h9778, hc01, hc23, hlam, hphi, ht12, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h10064, h10068, h10070, h7594, hc01, hc23, hlam, hphi, ht12, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h0, h10064, h10068, h10070, h7594, hc01, hc23, hlam, hphi, ht12, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h9992, hlam, p10098_0]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [h9993, hlam, p10098_1]
                          · have p10098_0 := h10098c.1
                            have p10098_1 := h10098c.2.1
                            have p10098_2 := h10098c.2.2.1
                            have p10098_3 := h10098c.2.2.2
                            linarith only [hlam, p10098_0]
                      · linarith only [h10062, h10070, h6852, h9993, hlam]
                    · linarith only [h10069, h5743, h9992, h9994, hlam]
                  · linarith only [h0, h10068, h9991, h9994, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · linarith only [h10067, h5743, h9992, hlam]
              · linarith only [h10066, h5743, h9991, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10129 | h10129
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10130 | h10130
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10131 | h10131
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10132 | h10132
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10133 | h10133
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10134 | h10134
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10135 | h10135
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10136 | h10136
                      · linarith only [h0, h10130, h10136, h9441, h9993, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10138 | h10138
                        · linarith only [h10129, h10136, h10138, h8272, h9991, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c | h10140c
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [hlam, p10140_0]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h0, hlam, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h5743, hlam, p10140_0]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h6852, hlam, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h7594, hlam, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h9441, hc01, hc24, hlam, hphi, ht12, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [hlam, p10140_0]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h8272, hlam, p10140_0]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h9441, hlam, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h9778, hlam, p10140_0]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h10129, h8272, hc01, hc12, hlam, hphi, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h10129, h8272, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [hlam, p10140_0]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h0, h10129, h8272, h9441, hc01, hc12, hlam, hphi, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h0, h10129, h8272, h9441, h9993, hc01, hc12, hlam, hphi, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h10132, h6852, hc01, hc13, hlam, hphi, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h0, h10136, h9441, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h9991, hlam, p10140_0]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [hlam, p10140_0]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h9993, hlam, p10140_0]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h10133, h7594, hc01, hc13, hlam, hphi, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h0, h10131, h10133, h9778, hc01, hc13, hlam, hphi, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h9992, hlam, p10140_0]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [h10129, h8272, h9992, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10140_1]
                          · have p10140_0 := h10140c.1
                            have p10140_1 := h10140c.2.1
                            have p10140_2 := h10140c.2.2.1
                            have p10140_3 := h10140c.2.2.2
                            linarith only [hlam, p10140_0]
                    · linarith only [h10135, h8272, h9992, hlam]
                  · linarith only [h10134, h8272, h9991, hlam]
                · linarith only [h10133, h5743, h8272, h9992, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h10129, h10132, h8272, h9991, hlam]
            · linarith only [h0, h10129, h10131, h8272, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h10129, h10130, h8272, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10172 | h10172
          · linarith only [h0, h10129, h10172, h9441, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10174 | h10174
            · linarith only [h0, h10129, h10174, h9778, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10176 | h10176
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10177 | h10177
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10178 | h10178
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10179 | h10179
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10180 | h10180
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10181 | h10181
                        · linarith only [h10181, h9991, h9993, hlam]
                        · rcases h0bigk with h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c | h10183c
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [hlam, p10183_0]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h0, hlam, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h5743, hlam, p10183_0]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h6852, hlam, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h7594, hlam, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h0, h10174, h10178, h10180, hc01, hc23, hlam, hphi, ht12, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [hlam, p10183_0]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h8272, hlam, p10183_0]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h9441, hlam, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h9778, hlam, p10183_0]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h10129, h5743, hc01, hc23, hlam, hphi, ht12, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h10129, h5743, hc02, hc23, hlam, hphi, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [hlam, p10183_0]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h10129, h5743, h6852, hc01, hc23, hlam, hphi, ht12, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h10129, h5743, h7594, hc01, hc23, hlam, hphi, ht12, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h6852, hc01, hc14, hlam, hphi, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h0, h10178, h9441, hc01, hc23, hlam, hphi, ht12, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h9991, hlam, p10183_0]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [hlam, p10183_0]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h9993, hlam, p10183_0]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h7594, hc01, hc15, hlam, hphi, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h0, h10178, h10180, h9778, hc01, hc23, hlam, hphi, ht12, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h9992, hlam, p10183_0]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [h10178, h10180, h9993, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10183_1]
                          · have p10183_0 := h10183c.1
                            have p10183_1 := h10183c.2.1
                            have p10183_2 := h10183c.2.2.1
                            have p10183_3 := h10183c.2.2.2
                            linarith only [hlam, p10183_0]
                      · linarith only [h0, h10172, h10180, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h10129, h10179, h5743, h9992, hlam]
                  · linarith only [h10129, h10178, h5743, h9991, hlam]
                · linarith only [h10177, h5743, h9992, hlam]
              · linarith only [h10176, h5743, h9991, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10214 | h10214
      · linarith only [h10214, h9991, h9992, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10216 | h10216
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10217 | h10217
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10218 | h10218
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10219 | h10219
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10220 | h10220
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10221 | h10221
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10222 | h10222
                    · linarith only [h10216, h10222, h9991, h9992, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h10216, h10220, h10222, h8272, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h10216, h10221, h5743, h8272, h9991, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10226 | h10226
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10227 | h10227
                    · linarith only [h10216, h10220, h10227, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10229 | h10229
                      · linarith only [h10214, h10217, h10229, h6852, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10231 | h10231
                        · linarith only [h0, h10229, h10231, h9441, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c | h10233c
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [hlam, p10233_0]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h0, hlam, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h5743, hlam, p10233_0]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h6852, hlam, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h7594, hlam, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h9441, hc01, hc24, hlam, hphi, ht12, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [hlam, p10233_0]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h8272, hlam, p10233_0]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h9441, hlam, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h9778, hlam, p10233_0]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h10216, h10220, h10231, h8272, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h10216, h10220, h10231, h8272, hc02, hc45, hlam, hphi, ht23, ht34, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [hlam, p10233_0]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h10216, h10220, h10231, h8272, hc04, hc45, hlam, hphi, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h9992, hlam, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h10219, h10220, h10231, h6852, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h0, h10219, h10220, h10231, h6852, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h9991, hlam, p10233_0]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [hlam, p10233_0]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h10214, hlam, p10233_0]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h10218, h9778, hc01, hc12, hlam, hphi, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h0, h10218, h9778, hc01, hc12, hlam, hphi, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h10218, h9778, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [h0, h10216, h10218, h10220, h10231, h8272, h9778, hc01, hc04, hc12, hc45, hlam, hphi, p10233_1]
                          · have p10233_0 := h10233c.1
                            have p10233_1 := h10233c.2.1
                            have p10233_2 := h10233c.2.2.1
                            have p10233_3 := h10233c.2.2.2
                            linarith only [hlam, p10233_0]
                  · linarith only [h0, h10226, h5743, h8272, h9991, hc01, hc13, hlam, hphi]
              · linarith only [h10216, h10219, h8272, h9991, hlam]
            · linarith only [h0, h10216, h10218, h8272, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h10216, h10217, h8272, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10263 | h10263
          · linarith only [h0, h10216, h10263, h9441, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10265 | h10265
            · linarith only [h0, h10263, h10265, h9778, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10267 | h10267
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10268 | h10268
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10269 | h10269
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10270 | h10270
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10271 | h10271
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10272 | h10272
                        · linarith only [h10216, h10268, h10272, h9991, h9992, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases h0bigk with h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c | h10274c
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [hlam, p10274_0]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h0, hlam, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h5743, hlam, p10274_0]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h6852, hlam, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h7594, hlam, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h0, h10265, h10269, h10271, hc01, hc23, hlam, hphi, ht12, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [hlam, p10274_0]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h8272, hlam, p10274_0]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h9441, hlam, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h9778, hlam, p10274_0]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h10269, h10271, h10272, h9992, hc01, hc23, hlam, hphi, ht12, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h10269, h10271, h10272, h9992, hc02, hc23, hlam, hphi, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [hlam, p10274_0]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h10269, h10271, h10272, h9992, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h9992, hlam, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h6852, hc01, hc14, hlam, hphi, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h0, h10269, h9441, hc01, hc23, hlam, hphi, ht12, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h9991, hlam, p10274_0]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [hlam, p10274_0]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h10214, hlam, p10274_0]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h10269, h10271, h10272, h9992, hc01, hc23, hlam, hphi, ht12, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h0, h10269, h10271, h10272, h9992, hc01, hc23, hlam, hphi, ht12, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h10269, h10271, h10272, h9992, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [h10269, h10271, h10272, h9992, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10274_1]
                          · have p10274_0 := h10274c.1
                            have p10274_1 := h10274c.2.1
                            have p10274_2 := h10274c.2.2.1
                            have p10274_3 := h10274c.2.2.2
                            linarith only [hlam, p10274_0]
                      · linarith only [h0, h10263, h10271, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h10216, h10268, h10270, hlam]
                  · linarith only [h10216, h10268, h10269, h9991, h9992, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10303 | h10303
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10304 | h10304
                    · linarith only [h10268, h10304, h5743, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h10216, h10304, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10216, h10303, h9991, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
              · linarith only [h10267, h9991, h9992, hc13, hc35, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10309 | h10309
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10310 | h10310
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10311 | h10311
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10312 | h10312
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10313 | h10313
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10314 | h10314
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10315 | h10315
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10316 | h10316
                  · linarith only [h10309, h10311, h10316, h9991, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h10314, h10316, h8272, hc01, hc13, hlam, hphi]
                · linarith only [h10309, h10315, h5743, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10320 | h10320
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10321 | h10321
                  · linarith only [h10311, h10314, h10321, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10323 | h10323
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10324 | h10324
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10325 | h10325
                        · rcases h0bigk with h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c | h10326c
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [hlam, p10326_0]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h0, hlam, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h5743, hlam, p10326_0]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h6852, hlam, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h7594, hlam, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h10313, h10314, h10320, h9778, hc01, hc34, hlam, hphi, ht12, ht23, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [hlam, p10326_0]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h8272, hlam, p10326_0]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h9441, hlam, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h9778, hlam, p10326_0]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h10311, h10314, h8272, hc01, hc34, hlam, hphi, ht12, ht23, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h10311, h10314, h8272, hc02, hc34, hlam, hphi, ht23, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [hlam, p10326_0]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h9991, hlam, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h10311, h10314, h8272, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h10312, h9441, hc01, hc12, hlam, hphi, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h0, h10312, h9441, hc01, hc12, hlam, hphi, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h10312, h9441, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [hlam, p10326_0]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h0, h10312, h9441, h9778, hc01, hc12, hlam, hphi, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h10314, h10320, h7594, hc01, hc34, hlam, hphi, ht12, ht23, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h0, h10313, h10314, h10320, h9778, hc01, hc34, hlam, hphi, ht12, ht23, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h10309, hlam, p10326_0]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [h10310, hlam, p10326_1]
                          · have p10326_0 := h10326c.1
                            have p10326_1 := h10326c.2.1
                            have p10326_2 := h10326c.2.2.1
                            have p10326_3 := h10326c.2.2.2
                            linarith only [hlam, p10326_0]
                        · linarith only [h10314, h10325, h5743, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h10309, h10310, h10314, h10324, h5743, h9441, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h10309, h10323, h8272, hlam]
                · linarith only [h10309, h10311, h10320, h8272, hlam]
            · linarith only [h0, h10311, h10313, h8272, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h10311, h10312, h8272, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10358 | h10358
          · linarith only [h0, h10311, h10358, h9441, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10360 | h10360
            · linarith only [h0, h10311, h10360, h9778, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10362 | h10362
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10363 | h10363
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10364 | h10364
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10365 | h10365
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10366 | h10366
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10367 | h10367
                        · rcases h0bigk with h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c | h10368c
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [hlam, p10368_0]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h0, hlam, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h5743, hlam, p10368_0]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h6852, hlam, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h7594, hlam, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h0, h10360, h10364, h10366, hc01, hc23, hlam, hphi, ht12, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [hlam, p10368_0]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h8272, hlam, p10368_0]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h9441, hlam, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h9778, hlam, p10368_0]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h10311, h10362, h9991, hc01, hc23, hlam, hphi, ht12, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h10311, h10362, h9991, hc02, hc23, hlam, hphi, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [hlam, p10368_0]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h9991, hlam, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h10311, h10362, h9991, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h6852, hc01, hc14, hlam, hphi, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h0, h10364, h9441, hc01, hc23, hlam, hphi, ht12, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h10311, h10362, h9991, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [hlam, p10368_0]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h0, h10311, h10362, h9778, h9991, hc01, hc23, hlam, hphi, ht12, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h7594, hc01, hc15, hlam, hphi, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h0, h10364, h10366, h9778, hc01, hc23, hlam, hphi, ht12, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h10309, hlam, p10368_0]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [h10310, hlam, p10368_1]
                          · have p10368_0 := h10368c.1
                            have p10368_1 := h10368c.2.1
                            have p10368_2 := h10368c.2.2.1
                            have p10368_3 := h10368c.2.2.2
                            linarith only [hlam, p10368_0]
                        · linarith only [h10310, h10367, h9991, hlam]
                      · linarith only [h10309, h10310, h10311, h10358, h10362, h10366, h6852, h9991, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h10309, h10311, h10362, h10365, h9991, hlam]
                  · linarith only [h10311, h10362, h10364, hlam]
                · linarith only [h10309, h10362, h10363, h9991, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10399 | h10399
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10400 | h10400
                  · linarith only [h0, h10360, h10362, h10399, h10400, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h10311, h10400, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h10309, h10399, h5743, hlam]
      · linarith only [h10309, h10310, h9991, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10405 | h10405
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10406 | h10406
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10407 | h10407
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10408 | h10408
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10409 | h10409
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10410 | h10410
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10411 | h10411
                  · linarith only [h0, h10406, h10411, h8272, h9991, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h10409, h10411, h8272, hc01, hc13, hlam, hphi]
                · linarith only [h0, h10409, h10410, h8272, h9991, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10415 | h10415
                · linarith only [h0, h10309, h10409, h10415, h8272, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10417 | h10417
                  · linarith only [h10409, h10417, h5743, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10419 | h10419
                    · linarith only [h10406, h10415, h10419, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10421 | h10421
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10422 | h10422
                        · rcases h0bigk with h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c | h10423c
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [hlam, p10423_0]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h0, hlam, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h5743, hlam, p10423_0]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h6852, hlam, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h7594, hlam, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h10406, h8272, hc01, hc13, hlam, hphi, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [hlam, p10423_0]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h8272, hlam, p10423_0]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h9441, hlam, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h9778, hlam, p10423_0]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h10415, h10422, h5743, hc01, hc34, hlam, hphi, ht12, ht23, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h10406, h10415, h10422, h8272, hc02, hc34, hlam, hphi, ht23, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [hlam, p10423_0]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h9991, hlam, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h10309, hlam, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h6852, hc01, hc14, hlam, hphi, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h0, h10407, h9441, hc01, hc12, hlam, hphi, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h10407, h9441, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [hlam, p10423_0]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h10407, h9441, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h7594, hc01, hc15, hlam, hphi, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h0, h10408, h9778, hc01, hc15, hlam, hphi, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h0, h10309, h10422, h8272, hc01, hc34, hlam, hphi, ht12, ht23, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [h10405, hlam, p10423_1]
                          · have p10423_0 := h10423c.1
                            have p10423_1 := h10423c.2.1
                            have p10423_2 := h10423c.2.2.1
                            have p10423_3 := h10423c.2.2.2
                            linarith only [hlam, p10423_0]
                        · linarith only [h10405, h10407, h10409, h10422, h6852, h9441, hc01, hc12, hlam, hphi]
                      · linarith only [h10405, h10421, h9441, hlam]
            · linarith only [h0, h10407, h10408, h9441, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h10406, h10407, h8272, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10453 | h10453
          · linarith only [h0, h10406, h10453, h9441, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10455 | h10455
            · linarith only [h0, h10406, h10455, h9778, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10457 | h10457
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10458 | h10458
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10459 | h10459
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10460 | h10460
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10461 | h10461
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10462 | h10462
                        · rcases h0bigk with h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c | h10463c
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [hlam, p10463_0]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h0, hlam, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h5743, hlam, p10463_0]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h6852, hlam, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h7594, hlam, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h0, h10455, h10459, h10461, hc01, hc23, hlam, hphi, ht12, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [hlam, p10463_0]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h8272, hlam, p10463_0]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h9441, hlam, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h9778, hlam, p10463_0]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h10406, h5743, hc01, hc23, hlam, hphi, ht12, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h10406, h5743, hc02, hc23, hlam, hphi, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [hlam, p10463_0]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h9991, hlam, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h10309, hlam, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h10406, h10457, h9991, hc01, hc23, hlam, hphi, ht12, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h0, h10406, h10457, h9991, hc01, hc23, hlam, hphi, ht12, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h10406, h10457, h9991, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [hlam, p10463_0]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h10406, h10457, h9991, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h7594, hc01, hc15, hlam, hphi, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h0, h10459, h10461, h9778, hc01, hc23, hlam, hphi, ht12, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h0, h10309, h10406, h10457, h10462, h8272, hc01, hc23, hlam, hphi, ht12, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [h10405, hlam, p10463_1]
                          · have p10463_0 := h10463c.1
                            have p10463_1 := h10463c.2.1
                            have p10463_2 := h10463c.2.2.1
                            have p10463_3 := h10463c.2.2.2
                            linarith only [hlam, p10463_0]
                        · linarith only [h10405, h10462, h9991, hlam]
                      · linarith only [h0, h10405, h10406, h10457, h10461, h9441, h9991, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h10406, h10457, h10460, h8272, h9991, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h10406, h10457, h10459, hlam]
                · linarith only [h0, h10457, h10458, h8272, h9991, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10494 | h10494
                · linarith only [h0, h10309, h10457, h10494, h8272, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10496 | h10496
                  · linarith only [h10457, h10496, h5743, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h10406, h10496, hc01, hc34, hlam, hphi, ht12, ht23]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10499 | h10499
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10500 | h10500
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10501 | h10501
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10502 | h10502
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10503 | h10503
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10504 | h10504
                  · linarith only [h0, h10499, h10504, h8272, h9991, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h10502, h10504, h8272, hc01, hc13, hlam, hphi]
                · linarith only [h0, h10502, h10503, h8272, h9991, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10508 | h10508
                · linarith only [h0, h10309, h10502, h10508, h8272, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10510 | h10510
                  · linarith only [h10502, h10510, h5743, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10512 | h10512
                    · linarith only [h10499, h10508, h10512, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10514 | h10514
                      · linarith only [h10405, h10500, h10514, h6852, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10516 | h10516
                        · linarith only [h0, h10514, h10516, h9441, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h10499, h10502, h10516, h8272, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h10499, h10501, h8272, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h10499, h10500, h8272, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10521 | h10521
          · linarith only [h0, h10499, h10521, h9441, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10523 | h10523
            · linarith only [h0, h10499, h10523, h9778, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10525 | h10525
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10526 | h10526
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10527 | h10527
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10528 | h10528
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10529 | h10529
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10530 | h10530
                        · linarith only [h0, h10405, h10525, h10530, h8272, h9991, hc01, hc13, hlam, hphi]
                        · linarith only [h0, h10527, h10529, h10530, h8272, h9991, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h10521, h10529, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h10499, h10526, h10528, hlam]
                  · linarith only [h0, h10309, h10499, h10526, h10527, h8272, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h10525, h10526, h8272, h9991, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10537 | h10537
                · linarith only [h0, h10309, h10525, h10537, h8272, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10539 | h10539
                  · linarith only [h10525, h10539, h5743, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h10499, h10539, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8272 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h9441 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 2 5 (by decide) (by decide) with h9778 | h9778
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594 h8272 h9441 h9778
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594 h8272 h9441 h9778

set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8272 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 2 4 (by decide) (by decide) with h9441 | h9441
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594 h8272 h9441
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594 h8272 h9441

set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 2 3 (by decide) (by decide) with h8272 | h8272
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594 h8272
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594 h8272

set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 1 5 (by decide) (by decide) with h7594 | h7594
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x0 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594

end R2N4
