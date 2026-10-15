import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8735 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8736 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8737 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8738 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 3 5 (by decide) (by decide) with h9297 | h9297
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9298 | h9298
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9299 | h9299
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9300 | h9300
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9301 | h9301
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9302 | h9302
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9303 | h9303
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9304 | h9304
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9305 | h9305
                  · linarith only [h8735, h8738, h9297, h9305, hc02, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9307 | h9307
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9308 | h9308
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9309 | h9309
                        · rcases h0bigk with h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c | h9310c
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [hlam, p9310_0]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h0, hlam, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h6253, hlam, p9310_0]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h7338, hlam, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h8081, hlam, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [hlam, p9310_0]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h0, h8735, h9307, h9309, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h0, h8735, h8738, h9307, h9309, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h8738, h9302, hc01, hc13, hlam, hphi, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h8735, hlam, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [hlam, p9310_0]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h8738, hlam, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h8081, h8738, h9302, hc01, hc13, hlam, hphi, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h7338, hc01, hc14, hlam, hphi, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h8736, hlam, p9310_0]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h8738, h9302, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [hlam, p9310_0]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h8081, h8738, h9302, hc01, hc13, hlam, hphi, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h8081, hc01, hc15, hlam, hphi, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h8737, hlam, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h9297, hlam, p9310_0]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [h9298, hlam, p9310_1]
                          · have p9310_0 := h9310c.1
                            have p9310_1 := h9310c.2.1
                            have p9310_2 := h9310c.2.2.1
                            have p9310_3 := h9310c.2.2.2
                            linarith only [hlam, p9310_0]
                        · linarith only [h8738, h9298, h9309, hlam]
                      · linarith only [h8738, h9297, h9298, h9299, h9302, h9305, h9307, h9308, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h8738, h9297, h9299, h9302, h9307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h7338, h8738, h9297, h9298, h9299, h9302, h9304, hc01, hc12, hlam, hphi]
              · linarith only [h8738, h9297, h9302, h9303, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9341 | h9341
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9342 | h9342
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9343 | h9343
                  · linarith only [h6253, h9302, h9343, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9345 | h9345
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9346 | h9346
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9347 | h9347
                        · rcases h0bigk with h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c | h9348c
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [hlam, p9348_0]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h0, hlam, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h6253, hlam, p9348_0]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h7338, hlam, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h8081, hlam, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [hlam, p9348_0]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h0, h8735, h9345, h9347, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h6253, hc01, hc13, hlam, hphi, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h8735, hlam, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [hlam, p9348_0]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h8738, hlam, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h6253, h8081, h9302, hc01, hc34, hlam, hphi, ht12, ht23, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h7338, hc01, hc14, hlam, hphi, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h8736, hlam, p9348_0]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h8738, hc03, hc34, hlam, hphi, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [hlam, p9348_0]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h8081, h8738, hc01, hc34, hlam, hphi, ht12, ht23, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h8081, hc01, hc15, hlam, hphi, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h8737, hlam, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h9297, hlam, p9348_0]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [h9298, hlam, p9348_1]
                          · have p9348_0 := h9348c.1
                            have p9348_1 := h9348c.2.1
                            have p9348_2 := h9348c.2.2.1
                            have p9348_3 := h9348c.2.2.2
                            linarith only [hlam, p9348_0]
                        · linarith only [h6253, h9302, h9347, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h9343, h9345, h9346, hlam]
                    · linarith only [h6253, h9297, h9302, h9345, hc23, hc34, hlam, hphi]
                · linarith only [h7338, h8738, h9297, h9298, h9342, hlam]
              · linarith only [h6253, h7338, h8738, h9297, h9341, hc01, hc14, hlam, hphi]
          · linarith only [h0, h8737, h9301, hlam]
        · linarith only [h0, h8736, h9300, hlam]
      · linarith only [h0, h8735, h9299, hlam]
    · linarith only [h8738, h9297, h9298, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9383 | h9383
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9384 | h9384
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9385 | h9385
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9386 | h9386
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9387 | h9387
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9388 | h9388
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9389 | h9389
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9390 | h9390
                  · linarith only [h8735, h8738, h9390, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9392 | h9392
                    · linarith only [h0, h6253, h8735, h9297, h9392, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9394 | h9394
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9395 | h9395
                        · rcases h0bigk with h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c | h9396c
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [hlam, p9396_0]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h0, hlam, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h6253, hlam, p9396_0]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h7338, hlam, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h8081, hlam, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [hlam, p9396_0]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h0, h8736, h9394, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h0, h6253, h9297, hc01, hc12, hlam, hphi, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h9297, h9388, hc01, hc15, hlam, hphi, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h8735, hlam, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [hlam, p9396_0]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h8738, hlam, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h9297, hlam, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h7338, h9384, h9387, hc01, hc12, hlam, hphi, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h8736, hlam, p9396_0]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h6253, h7338, h9384, h9387, hc01, hc12, hlam, hphi, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [hlam, p9396_0]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h6253, h7338, h9297, h9384, h9387, hc01, hc12, hlam, hphi, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h8081, hc01, hc15, hlam, hphi, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h8737, hlam, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h6253, h9297, h9395, hc01, hc34, hlam, hphi, ht12, ht23, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [h9383, hlam, p9396_1]
                          · have p9396_0 := h9396c.1
                            have p9396_1 := h9396c.2.1
                            have p9396_2 := h9396c.2.2.1
                            have p9396_3 := h9396c.2.2.2
                            linarith only [hlam, p9396_0]
                        · linarith only [h0, h7338, h8736, h8738, h9394, h9395, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9423 | h9423
                        · rcases h0bigk with h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c | h9424c
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [hlam, p9424_0]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h0, hlam, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h6253, hlam, p9424_0]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h7338, hlam, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h8081, hlam, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [hlam, p9424_0]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h0, h9383, h9390, h9394, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h0, h9383, h9390, h9394, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h6253, h9384, hc01, hc12, hlam, hphi, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h8735, hlam, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [hlam, p9424_0]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h8738, hlam, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h9297, hlam, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h7338, h9384, h9387, hc01, hc12, hlam, hphi, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h8736, hlam, p9424_0]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h8738, h9384, h9387, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [hlam, p9424_0]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h8738, h9383, h9384, h9387, h9390, h9394, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h8081, h9384, h9387, h9389, hc01, hc12, hlam, hphi, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h8737, hlam, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h6253, h9297, h9384, h9387, h9423, hc01, hc12, hlam, hphi, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [h9383, hlam, p9424_1]
                          · have p9424_0 := h9424c.1
                            have p9424_1 := h9424c.2.1
                            have p9424_2 := h9424c.2.2.1
                            have p9424_3 := h9424c.2.2.2
                            linarith only [hlam, p9424_0]
                        · linarith only [h8738, h9383, h9423, hlam]
                · linarith only [h7338, h8738, h9383, h9389, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h6253, h8738, h9387, h9388, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9453 | h9453
              · linarith only [h6253, h9297, h9387, h9453, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9455 | h9455
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9456 | h9456
                  · linarith only [h6253, h9387, h9456, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9458 | h9458
                    · linarith only [h6253, h9453, h9458, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9460 | h9460
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9461 | h9461
                        · rcases h0bigk with h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [hlam, p9462_0]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h0, hlam, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h6253, hlam, p9462_0]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h7338, hlam, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h8081, hlam, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [hlam, p9462_0]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h6253, hc01, hc13, hlam, hphi, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h8735, hlam, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [hlam, p9462_0]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h8738, hlam, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h9297, hlam, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h7338, hc01, hc14, hlam, hphi, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h8736, hlam, p9462_0]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h8738, hc03, hc34, hlam, hphi, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [hlam, p9462_0]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h6253, h8738, h9297, hc01, hc34, hlam, hphi, ht12, ht23, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h8081, hc01, hc15, hlam, hphi, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h8737, hlam, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h6253, h9297, h9461, hc01, hc34, hlam, hphi, ht12, ht23, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [h9383, hlam, p9462_1]
                          · have p9462_0 := h9462c.1
                            have p9462_1 := h9462c.2.1
                            have p9462_2 := h9462c.2.2.1
                            have p9462_3 := h9462c.2.2.2
                            linarith only [hlam, p9462_0]
                        · linarith only [h7338, h9383, h9387, h9461, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9489 | h9489
                        · rcases h0bigk with h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c | h9490c
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [hlam, p9490_0]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h0, hlam, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h6253, hlam, p9490_0]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h7338, hlam, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h8081, hlam, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [hlam, p9490_0]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h0, h9383, h9456, h9460, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h6253, hc01, hc13, hlam, hphi, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h8735, hlam, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [hlam, p9490_0]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h8738, hlam, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h9297, hlam, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h7338, h9387, hc01, hc34, hlam, hphi, ht12, ht23, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h8736, hlam, p9490_0]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h7338, h9387, hc03, hc34, hlam, hphi, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [hlam, p9490_0]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h6253, h7338, h9297, h9387, hc01, hc34, hlam, hphi, ht12, ht23, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h8081, h9387, h9455, hc01, hc34, hlam, hphi, ht12, ht23, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h8737, hlam, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h6253, h8081, h9387, h9455, hc01, hc34, hlam, hphi, ht12, ht23, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [h9383, hlam, p9490_1]
                          · have p9490_0 := h9490c.1
                            have p9490_1 := h9490c.2.1
                            have p9490_2 := h9490c.2.2.1
                            have p9490_3 := h9490c.2.2.2
                            linarith only [hlam, p9490_0]
                        · linarith only [h7338, h9383, h9387, h9489, hlam]
                · linarith only [h7338, h9383, h9455, hlam]
          · linarith only [h0, h8737, h9386, hlam]
        · linarith only [h0, h8736, h9385, hlam]
      · linarith only [h0, h8735, h9384, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9521 | h9521
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9522 | h9522
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9523 | h9523
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9524 | h9524
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9525 | h9525
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9526 | h9526
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9527 | h9527
                  · linarith only [h8735, h8738, h9527, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9529 | h9529
                    · linarith only [h8735, h9297, h9529, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9531 | h9531
                      · linarith only [h8736, h9383, h9531, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9533 | h9533
                        · linarith only [h7338, h9383, h9521, h9524, h9533, hc01, hc12, hlam, hphi]
                        · linarith only [h6253, h8738, h9521, h9524, h9526, h9533, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9536 | h9536
                  · linarith only [h0, h6253, h8735, h8738, h9536, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9538 | h9538
                    · linarith only [h8735, h9297, h9538, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9540 | h9540
                      · linarith only [h8736, h8738, h9297, h9383, h9524, h9526, h9540, hc03, hc35, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9542 | h9542
                        · linarith only [h9524, h9526, h9542, hlam]
                        · rcases h0bigk with h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c | h9544c
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [hlam, p9544_0]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h0, hlam, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h6253, hlam, p9544_0]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h7338, hlam, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h8081, hlam, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [hlam, p9544_0]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h8738, h9524, hc01, hc14, hlam, hphi, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h8735, hlam, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [hlam, p9544_0]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h8738, hlam, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h9297, hlam, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h7338, h9526, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h8736, hlam, p9544_0]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h8738, h9524, h9526, hc03, hc45, hlam, hphi, ht34, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [hlam, p9544_0]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h9383, hlam, p9544_0]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h8081, hc01, hc15, hlam, hphi, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h8737, hlam, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h6253, h9297, hc01, hc35, hlam, hphi, ht12, ht23, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [h9383, hc04, hc45, hlam, hphi, p9544_1]
                          · have p9544_0 := h9544c.1
                            have p9544_1 := h9544c.2.1
                            have p9544_2 := h9544c.2.2.1
                            have p9544_3 := h9544c.2.2.2
                            linarith only [hlam, p9544_0]
              · linarith only [h6253, h8738, h9524, h9525, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9571 | h9571
              · linarith only [h6253, h9297, h9524, h9571, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9573 | h9573
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9574 | h9574
                  · linarith only [h6253, h9524, h9574, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9576 | h9576
                    · linarith only [h8735, h9297, h9576, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9578 | h9578
                      · linarith only [h0, h7338, h8736, h9383, h9578, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9580 | h9580
                        · rcases h0bigk with h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c | h9581c
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [hlam, p9581_0]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h0, hlam, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h6253, hlam, p9581_0]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h7338, hlam, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h8081, hlam, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [hlam, p9581_0]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h6253, hc01, hc13, hlam, hphi, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h8735, hlam, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [hlam, p9581_0]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h8738, hlam, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h9297, hlam, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h7338, h9524, hc01, hc34, hlam, hphi, ht12, ht23, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h8736, hlam, p9581_0]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h7338, h9524, hc03, hc34, hlam, hphi, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [hlam, p9581_0]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h9383, hlam, p9581_0]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h8081, h9524, h9573, hc01, hc34, hlam, hphi, ht12, ht23, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h8737, hlam, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h6253, h8081, h9524, h9573, hc01, hc34, hlam, hphi, ht12, ht23, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [h9383, h9524, h9573, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p9581_1]
                          · have p9581_0 := h9581c.1
                            have p9581_1 := h9581c.2.1
                            have p9581_2 := h9581c.2.2.1
                            have p9581_3 := h9581c.2.2.2
                            linarith only [hlam, p9581_0]
                        · linarith only [h9524, h9573, h9580, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9608 | h9608
                  · linarith only [h8735, h8738, h9608, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9610 | h9610
                    · linarith only [h6253, h8081, h8735, h9524, h9571, h9610, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9612 | h9612
                      · linarith only [h6253, h9524, h9573, h9612, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9614 | h9614
                        · linarith only [h6253, h9524, h9573, h9614, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h6253, h9524, h9614, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h8737, h9523, hlam]
        · linarith only [h0, h8736, h9522, hlam]
      · linarith only [h0, h8735, h9521, hlam]

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8735 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8736 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8737 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 3 4 (by decide) (by decide) with h8738 | h8738
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6253 hg7338 hg8081 h8735 h8736 h8737 h8738
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6253 hg7338 hg8081 h8735 h8736 h8737 h8738

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8735 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8736 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8737 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 3 4 (by decide) (by decide) with h9620 | h9620
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9621 | h9621
    · linarith only [h8735, h8737, h9621, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9623 | h9623
      · linarith only [h8736, h8737, h9623, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9625 | h9625
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9626 | h9626
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9627 | h9627
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9628 | h9628
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9629 | h9629
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9630 | h9630
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9631 | h9631
                    · linarith only [h8735, h8737, h9627, h9631, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h8735, h8737, h9620, h9627, h9631, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9634 | h9634
                    · linarith only [h8735, h8737, h9627, h9634, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h8735, h8737, h9620, h9627, h9634, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9637 | h9637
                  · linarith only [h7338, h9623, h9628, h9629, h9637, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9639 | h9639
                    · linarith only [h8735, h8737, h9627, h9639, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h8735, h8737, h9620, h9627, h9639, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h6253, h8735, h8737, h9620, h9627, h9628, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9643 | h9643
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9644 | h9644
                · linarith only [h9620, h9621, h9625, h9627, h9644, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9646 | h9646
                  · linarith only [h7338, h9623, h9626, h9627, h9646, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9648 | h9648
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9649 | h9649
                      · linarith only [h0, h8735, h9627, h9644, h9649, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9651 | h9651
                        · linarith only [h8736, h9623, h9651, hlam]
                        · linarith only [h0, h8735, h9627, h9648, h9651, hc34, hc45, hlam, hphi]
                    · linarith only [h9620, h9621, h9648, hc23, hc35, hlam, hphi]
              · linarith only [h6253, h9620, h9643, hlam]
          · linarith only [h0, h8736, h9626, hlam]
        · linarith only [h0, h8735, h9625, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9658 | h9658
    · linarith only [h8736, h8737, h9620, h9658, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9660 | h9660
      · linarith only [h8736, h8737, h9660, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9662 | h9662
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9663 | h9663
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9664 | h9664
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9665 | h9665
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9666 | h9666
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9667 | h9667
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9668 | h9668
                    · linarith only [h0, h6253, h8735, h9620, h9668, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9670 | h9670
                      · linarith only [h8736, h8737, h9658, h9664, h9668, h9670, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9672 | h9672
                        · linarith only [h8736, h8737, h9662, h9666, h9670, h9672, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9674 | h9674
                          · linarith only [h8736, h8737, h9668, h9672, h9674, hc23, hc34, hlam, hphi]
                          · linarith only [h6253, h9620, h9662, h9665, h9667, h9674, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9677 | h9677
                    · linarith only [h6253, h8735, h8737, h9620, h9677, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9679 | h9679
                      · linarith only [h8736, h8737, h9658, h9664, h9677, h9679, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9681 | h9681
                        · linarith only [h8736, h8737, h9662, h9666, h9667, h9679, h9681, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9683 | h9683
                          · linarith only [h9665, h9667, h9683, hlam]
                          · rcases h0bigk with h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c | h9685c
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [hlam, p9685_0]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h0, hlam, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h6253, hlam, p9685_0]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h7338, hlam, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h8081, hlam, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h8737, h9662, h9666, h9679, hc01, hc12, hlam, hphi, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [hlam, p9685_0]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h6253, h8737, h9662, h9666, h9679, hc01, hc12, hlam, hphi, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h8737, h9662, h9666, h9679, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h8737, hlam, p9685_0]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h9620, h9665, hc01, hc14, hlam, hphi, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h8735, hlam, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [hlam, p9685_0]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h9620, hlam, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h9658, hlam, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h7338, h8736, h8737, h9662, h9666, h9667, h9677, h9679, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h8736, hlam, p9685_0]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h8736, h8737, h9662, h9666, h9679, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [hlam, p9685_0]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h9660, hlam, p9685_0]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h8081, hc01, hc15, hlam, hphi, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h8737, h9662, h9666, h9679, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h6253, h8737, h9662, h9666, h9679, hc01, hc12, hlam, hphi, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [h8737, h9662, h9666, h9679, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9685_1]
                            · have p9685_0 := h9685c.1
                              have p9685_1 := h9685c.2.1
                              have p9685_2 := h9685c.2.2.1
                              have p9685_3 := h9685c.2.2.2
                              linarith only [hlam, p9685_0]
                · linarith only [h6253, h9620, h9665, h9666, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9712 | h9712
                · linarith only [h6253, h9658, h9665, h9712, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9714 | h9714
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9715 | h9715
                    · linarith only [h6253, h9665, h9715, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9717 | h9717
                      · linarith only [h8736, h8737, h9664, h9715, h9717, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9719 | h9719
                        · linarith only [h6253, h8736, h8737, h9620, h9660, h9664, h9719, hc01, hc12, hlam, hphi]
                        · linarith only [h8736, h8737, h9665, h9714, h9715, h9719, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9722 | h9722
                    · linarith only [h6253, h9665, h9722, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9724 | h9724
                      · linarith only [h8735, h8737, h9664, h9724, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9726 | h9726
                        · linarith only [h6253, h8736, h8737, h9664, h9665, h9714, h9726, hc01, hc12, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9728 | h9728
                          · linarith only [h6253, h9665, h9714, h9728, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h6253, h9665, h9728, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9731 | h9731
              · linarith only [h6253, h9620, h9662, h9664, h9731, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9733 | h9733
                · linarith only [h6253, h9658, h9663, h9664, h9731, h9733, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9735 | h9735
                  · linarith only [h6253, h9620, h9660, h9663, h9664, h9735, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9737 | h9737
                    · linarith only [h6253, h9731, h9737, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9739 | h9739
                      · linarith only [h0, h8081, h8736, h9664, h9733, h9737, h9739, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9741 | h9741
                        · linarith only [h0, h7338, h8736, h9660, h9741, hc01, hc12, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9743 | h9743
                          · linarith only [h0, h9664, h9741, h9743, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h6253, h9731, h9743, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h8736, h9663, hlam]
        · linarith only [h0, h8735, h9662, hlam]

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8735 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8736 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 2 5 (by decide) (by decide) with h8737 | h8737
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6253 hg7338 hg8081 h8735 h8736 h8737
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6253 hg7338 hg8081 h8735 h8736 h8737

end R2N4
