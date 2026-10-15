import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7248000 in
set_option maxHeartbeats 7248000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s8 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h6311 | h6311
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s9 m hb0 hb1 hb3 hb4 h0 h6310 h6311
  · rcases m.htr 0 1 5 (by decide) (by decide) with h9288 | h9288
    · rcases m.htr 0 2 3 (by decide) (by decide) with h9289 | h9289
      · rcases m.htr 0 2 4 (by decide) (by decide) with h9290 | h9290
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9291 | h9291
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9292 | h9292
            · linarith only [h6310, h6311, h9292, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9294 | h9294
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9295 | h9295
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9296 | h9296
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9297 | h9297
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9298 | h9298
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9299 | h9299
                        · linarith only [h6310, h9292, h9299, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9301 | h9301
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9302 | h9302
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9303 | h9303
                              · linarith only [h6310, h6311, h9296, h9299, h9303, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9305 | h9305
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9306 | h9306
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9307 | h9307
                                    · rcases h0bigk with h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [hlam, p9308_0]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h0, hlam, p9308_1]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h6311, h9299, hc03, hc34, hlam, hphi, p9308_1]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h6311, hlam, p9308_1]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        rcases p9308_3 (m.d 0 1) (by simp) with h9313 | h9313
                                        · rcases p9308_3 (m.d 0 2) (by simp) with h9314 | h9314
                                          · rcases p9308_3 (m.d 0 3) (by simp) with h9315 | h9315
                                            · linarith only [h6310, h9315, hlam]
                                            · linarith only [h9294, h9315, hlam]
                                          · linarith only [h9291, h9314, hlam]
                                        · linarith only [h9288, h9313, hlam]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h6310, h9296, h9305, h9307, hc45, hlam, hphi, ht0b, ht5b, p9308_1, u0elo1]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [hlam, p9308_0]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h6310, h9296, h9305, h9307, hc45, hlam, hphi, ht0b, ht5b, p9308_1, u0elo1]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h6310, h6311, h9296, h9305, h9307, hc45, hlam, hphi, ht0b, ht5b, p9308_1, u0elo1]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        rcases p9308_3 (m.d 0 1) (by simp) with h9324 | h9324
                                        · linarith only [h0, h9324, hlam]
                                        · linarith only [h9288, h9324, hlam]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h6310, hlam, p9308_1]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h9289, hlam, p9308_1]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [hlam, p9308_0]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h9292, hlam, p9308_1]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        rcases p9308_3 (m.d 0 1) (by simp) with h9331 | h9331
                                        · rcases p9308_3 (m.d 0 2) (by simp) with h9332 | h9332
                                          · rcases p9308_3 (m.d 0 3) (by simp) with h9333 | h9333
                                            · rcases p9308_3 (m.d 0 4) (by simp) with h9334 | h9334
                                              · rcases p9308_3 (m.d 0 5) (by simp) with h9335 | h9335
                                                · linarith only [h9294, h9335, hlam]
                                                · rcases h0emin with h9337 | h9337 | h9337 | h9337 | h9337
                                                  · rcases h1bigk with h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c | h9338c
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [hlam, p9338_0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h0, hlam, p9338_0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h9296, h9305, h9307, hc45, hlam, hphi, ht0b, ht5b, p9338_1, u0elo0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h6311, hlam, p9338_0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      rcases p9338_3 (m.d 0 1) (by simp) with h9343 | h9343
                                                      · rcases p9338_3 (m.d 1 2) (by simp) with h9344 | h9344
                                                        · rcases p9338_3 (m.d 1 3) (by simp) with h9345 | h9345
                                                          · linarith only [h6310, h9345, hlam]
                                                          · linarith only [h9301, h9345, hlam]
                                                        · linarith only [h9298, h9344, hlam]
                                                      · linarith only [h9343, hlam, p9338_0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h9337, hc12, hlam, ht01, p9338_1]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [hlam, p9338_0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      rcases p9338_3 (m.d 0 1) (by simp) with h9352 | h9352
                                                      · linarith only [h0, h9352, hlam]
                                                      · linarith only [h6310, h9352, hlam]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h6310, h6311, h9288, h9298, h9305, h9307, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9308_1, p9338_1]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h0, h6310, h9288, hlam, p9308_1, p9338_2]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h6310, hlam, p9338_0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h9296, hlam, p9338_1]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [hlam, p9338_0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h9299, hlam, p9338_1]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h6310, h9298, h9305, h9307, hc45, hlam, hphi, ht0b, ht5b, p9338_1, u0elo0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h9297, h9337, hc12, hlam, ht01, p9338_1]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h9297, hlam, p9338_1]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      rcases p9338_3 (m.d 0 1) (by simp) with h9364 | h9364
                                                      · linarith only [h6311, h9364, hlam]
                                                      · linarith only [h6310, h9364, hlam]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [hlam, p9338_0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h6310, h6311, h9288, hlam, p9308_1, p9338_2]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h9288, hlam, p9338_0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h9298, hlam, p9338_1]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h9301, hlam, p9338_0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [h9302, hlam, p9338_0]
                                                    · have p9338_0 := h9338c.1
                                                      have p9338_1 := h9338c.2.1
                                                      have p9338_2 := h9338c.2.2.1
                                                      have p9338_3 := h9338c.2.2.2
                                                      linarith only [hlam, p9338_0]
                                                  · rcases h1bigk with h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c | h9374c
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [hlam, p9374_0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h0, hlam, p9374_0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h9296, h9305, h9307, hc45, hlam, hphi, ht0b, ht5b, p9374_1, u0elo0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h6311, hlam, p9374_0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      rcases p9374_3 (m.d 0 1) (by simp) with h9379 | h9379
                                                      · rcases p9374_3 (m.d 1 2) (by simp) with h9380 | h9380
                                                        · rcases p9374_3 (m.d 1 3) (by simp) with h9381 | h9381
                                                          · linarith only [h6310, h9381, hlam]
                                                          · linarith only [h9301, h9381, hlam]
                                                        · linarith only [h9298, h9380, hlam]
                                                      · linarith only [h9379, hlam, p9374_0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h6310, h9296, h9305, h9307, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9374_1]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [hlam, p9374_0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      rcases p9374_3 (m.d 0 1) (by simp) with h9388 | h9388
                                                      · linarith only [h0, h9388, hlam]
                                                      · linarith only [h6310, h9388, hlam]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h6310, h6311, h9288, h9298, h9305, h9307, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9308_1, p9374_1]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h0, h6310, h9288, hlam, p9308_1, p9374_2]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h6310, hlam, p9374_0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h9296, hlam, p9374_1]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [hlam, p9374_0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h9299, hlam, p9374_1]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h6310, h9298, h9305, h9307, hc45, hlam, hphi, ht0b, ht5b, p9374_1, u0elo0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h6310, h9288, h9297, h9298, h9305, h9307, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9308_1, p9374_1]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h9297, hlam, p9374_1]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      rcases p9374_3 (m.d 0 1) (by simp) with h9400 | h9400
                                                      · linarith only [h6311, h9400, hlam]
                                                      · linarith only [h6310, h9400, hlam]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [hlam, p9374_0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h6310, h6311, h9288, hlam, p9308_1, p9374_2]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h9288, hlam, p9374_0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h9298, hlam, p9374_1]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h9301, hlam, p9374_0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [h9302, hlam, p9374_0]
                                                    · have p9374_0 := h9374c.1
                                                      have p9374_1 := h9374c.2.1
                                                      have p9374_2 := h9374c.2.2.1
                                                      have p9374_3 := h9374c.2.2.2
                                                      linarith only [hlam, p9374_0]
                                                  · rcases h1bigk with h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c | h9410c
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [hlam, p9410_0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h0, hlam, p9410_0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h9296, h9305, h9307, hc45, hlam, hphi, ht0b, ht5b, p9410_1, u0elo0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h6311, hlam, p9410_0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      rcases p9410_3 (m.d 0 1) (by simp) with h9415 | h9415
                                                      · rcases p9410_3 (m.d 1 2) (by simp) with h9416 | h9416
                                                        · rcases p9410_3 (m.d 1 3) (by simp) with h9417 | h9417
                                                          · linarith only [h6310, h9417, hlam]
                                                          · linarith only [h9301, h9417, hlam]
                                                        · linarith only [h9298, h9416, hlam]
                                                      · linarith only [h9415, hlam, p9410_0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h6310, h9296, h9305, h9307, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9410_1]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [hlam, p9410_0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      rcases p9410_3 (m.d 0 1) (by simp) with h9424 | h9424
                                                      · linarith only [h0, h9424, hlam]
                                                      · linarith only [h6310, h9424, hlam]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h6310, h6311, h9288, h9298, h9305, h9307, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9308_1, p9410_1]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h0, h6310, h9288, hlam, p9308_1, p9410_2]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h6310, hlam, p9410_0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h9296, hlam, p9410_1]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [hlam, p9410_0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h9299, hlam, p9410_1]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h6310, h9298, h9305, h9307, hc45, hlam, hphi, ht0b, ht5b, p9410_1, u0elo0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h6310, h9288, h9297, h9298, h9305, h9307, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9308_1, p9410_1]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h9297, hlam, p9410_1]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      rcases p9410_3 (m.d 0 1) (by simp) with h9436 | h9436
                                                      · linarith only [h6311, h9436, hlam]
                                                      · linarith only [h6310, h9436, hlam]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [hlam, p9410_0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h6310, h6311, h9288, hlam, p9308_1, p9410_2]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h9288, hlam, p9410_0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h9298, hlam, p9410_1]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h9301, hlam, p9410_0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [h9302, hlam, p9410_0]
                                                    · have p9410_0 := h9410c.1
                                                      have p9410_1 := h9410c.2.1
                                                      have p9410_2 := h9410c.2.2.1
                                                      have p9410_3 := h9410c.2.2.2
                                                      linarith only [hlam, p9410_0]
                                                  · rcases h1bigk with h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c | h9446c
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [hlam, p9446_0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h0, hlam, p9446_0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h9296, h9305, h9307, hc45, hlam, hphi, ht0b, ht5b, p9446_1, u0elo0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h6311, hlam, p9446_0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      rcases p9446_3 (m.d 0 1) (by simp) with h9451 | h9451
                                                      · rcases p9446_3 (m.d 1 2) (by simp) with h9452 | h9452
                                                        · rcases p9446_3 (m.d 1 3) (by simp) with h9453 | h9453
                                                          · linarith only [h6310, h9453, hlam]
                                                          · linarith only [h9301, h9453, hlam]
                                                        · linarith only [h9298, h9452, hlam]
                                                      · linarith only [h9451, hlam, p9446_0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h6310, h9296, h9305, h9307, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9446_1]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [hlam, p9446_0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      rcases p9446_3 (m.d 0 1) (by simp) with h9460 | h9460
                                                      · linarith only [h0, h9460, hlam]
                                                      · linarith only [h6310, h9460, hlam]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h6310, h6311, h9288, h9298, h9305, h9307, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9308_1, p9446_1]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h0, h6310, h9288, hlam, p9308_1, p9446_2]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h6310, hlam, p9446_0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h9296, hlam, p9446_1]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [hlam, p9446_0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h9299, hlam, p9446_1]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h6310, h9298, h9305, h9307, hc45, hlam, hphi, ht0b, ht5b, p9446_1, u0elo0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h6310, h9288, h9297, h9298, h9305, h9307, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9308_1, p9446_1]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h9297, hlam, p9446_1]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      rcases p9446_3 (m.d 0 1) (by simp) with h9472 | h9472
                                                      · linarith only [h6311, h9472, hlam]
                                                      · linarith only [h6310, h9472, hlam]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [hlam, p9446_0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h6310, h6311, h9288, hlam, p9308_1, p9446_2]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h9288, hlam, p9446_0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h9298, hlam, p9446_1]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h9301, hlam, p9446_0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [h9302, hlam, p9446_0]
                                                    · have p9446_0 := h9446c.1
                                                      have p9446_1 := h9446c.2.1
                                                      have p9446_2 := h9446c.2.2.1
                                                      have p9446_3 := h9446c.2.2.2
                                                      linarith only [hlam, p9446_0]
                                                  · linarith only [h6310, h9337, hlam, p9308_1, u0elo0]
                                              · linarith only [h9295, h9334, hlam]
                                            · linarith only [h9294, h9333, hlam]
                                          · linarith only [h9291, h9332, hlam]
                                        · linarith only [h9288, h9331, hlam]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h6310, h9290, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p9308_1, u0elo1]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h9290, hlam, p9308_0]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h9289, h9305, h9307, hc45, hlam, hphi, ht0b, ht5b, p9308_1, u0elo3]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [hlam, p9308_0]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        rcases p9308_3 (m.d 0 1) (by simp) with h9491 | h9491
                                        · linarith only [h6311, h9491, hlam]
                                        · linarith only [h9288, h9491, hlam]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h9288, hlam, p9308_0]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h9291, hlam, p9308_1]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h9294, hlam, p9308_0]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [h9295, hlam, p9308_1]
                                      · have p9308_0 := h9308c.1
                                        have p9308_1 := h9308c.2.1
                                        have p9308_2 := h9308c.2.2.1
                                        have p9308_3 := h9308c.2.2.2
                                        linarith only [hlam, p9308_0]
                                    · linarith only [h6310, h6311, h9299, h9307, hc13, hc45, hlam, hphi, ht34]
                                  · linarith only [h6310, h9301, h9302, h9303, h9305, h9306, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h6310, h6311, h9294, h9299, h9305, hc23, hc34, hlam, hphi]
                            · linarith only [h6310, h6311, h9302, hc13, hc45, hlam, hphi, ht34]
                          · linarith only [h9292, h9294, h9296, h9301, hc23, hc34, hlam, hphi]
                      · linarith only [h6311, h9291, h9297, h9298, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h9290, h9297, hlam]
                  · linarith only [h0, h9289, h9296, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h6311, h9288, h9295, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9508 | h9508
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9509 | h9509
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9510 | h9510
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9511 | h9511
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9512 | h9512
                        · linarith only [h6310, h9292, h9512, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9514 | h9514
                          · linarith only [h6310, h9294, h9514, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9516 | h9516
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9517 | h9517
                              · linarith only [h6311, h9288, h9509, h9512, h9514, h9517, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9519 | h9519
                                · linarith only [h6310, h9294, h9509, h9519, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9521 | h9521
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9522 | h9522
                                    · rcases h0bigk with h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c | h9523c
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [hlam, p9523_0]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h0, hlam, p9523_1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h6310, h6311, h9509, h9512, hc23, hc34, hlam, hphi, p9523_1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h6311, hlam, p9523_1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h6310, h6311, h9294, h9509, h9512, hc23, hc34, hlam, hphi, p9523_1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h6310, h9509, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9523_1, u0elo1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [hlam, p9523_0]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        rcases p9523_3 (m.d 0 1) (by simp) with h9531 | h9531
                                        · linarith only [h0, h9531, hlam]
                                        · linarith only [h6310, h9531, hlam]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h6311, h9288, h9509, h9514, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9523_1, u0elo1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        rcases p9523_3 (m.d 0 1) (by simp) with h9535 | h9535
                                        · linarith only [h0, h9535, hlam]
                                        · linarith only [h9288, h9535, hlam]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h6310, hlam, p9523_1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h9289, hlam, p9523_1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [hlam, p9523_0]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h9292, hlam, p9523_1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h9294, hlam, p9523_1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h9288, h9509, h9514, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9523_1, u0elo3]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h9290, hlam, p9523_0]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        rcases p9523_3 (m.d 0 1) (by simp) with h9545 | h9545
                                        · linarith only [h6311, h9545, hlam]
                                        · linarith only [h6310, h9545, hlam]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [hlam, p9523_0]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        rcases p9523_3 (m.d 0 1) (by simp) with h9549 | h9549
                                        · linarith only [h6311, h9549, hlam]
                                        · linarith only [h9288, h9549, hlam]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h9288, hlam, p9523_0]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h9291, hlam, p9523_1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h6310, h6311, h9288, h9509, h9512, hc23, hc34, hlam, hphi, p9523_1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [h9508, hlam, p9523_1]
                                      · have p9523_0 := h9523c.1
                                        have p9523_1 := h9523c.2.1
                                        have p9523_2 := h9523c.2.2.1
                                        have p9523_3 := h9523c.2.2.2
                                        linarith only [hlam, p9523_0]
                                    · linarith only [h6310, h6311, h9509, h9512, h9522, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h6311, h9288, h9512, h9516, h9517, h9521, hc23, hc34, hlam, hphi]
                            · linarith only [h6310, h6311, h9509, h9516, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h6310, h6311, h9291, h9509, h9510, h9511, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h9290, h9510, hlam]
                  · linarith only [h0, h9289, h9509, hlam]
                · linarith only [h6311, h9288, h9508, hlam]
          · linarith only [h0, h9288, h9291, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9565 | h9565
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9566 | h9566
            · linarith only [h0, h6310, h9290, h9566, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9568 | h9568
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9569 | h9569
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9570 | h9570
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9571 | h9571
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9572 | h9572
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9573 | h9573
                        · linarith only [h6310, h9566, h9573, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9575 | h9575
                          · linarith only [h0, h6310, h9290, h9571, h9575, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h6310, h9290, h9568, h9570, h9571, h9575, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h9290, h9571, h9572, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9579 | h9579
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9580 | h9580
                        · linarith only [h0, h6310, h9566, h9571, h9580, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9582 | h9582
                          · linarith only [h0, h6310, h9571, h9582, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h6310, h9568, h9570, h9571, h9582, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h0, h9565, h9579, hlam]
                  · linarith only [h0, h9289, h9570, hlam]
                · linarith only [h0, h6310, h9290, h9568, h9569, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9588 | h9588
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9589 | h9589
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9590 | h9590
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9591 | h9591
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9592 | h9592
                        · linarith only [h0, h6310, h9290, h9590, h9592, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9594 | h9594
                          · linarith only [h0, h6310, h9290, h9568, h9590, h9594, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9596 | h9596
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9597 | h9597
                              · linarith only [h0, h6310, h9288, h9290, h9589, h9590, h9592, h9597, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9599 | h9599
                                · linarith only [h0, h9288, h9290, h9568, h9589, h9590, h9594, h9599, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9601 | h9601
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9602 | h9602
                                    · rcases h0bigk with h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c | h9603c
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [hlam, p9603_0]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h0, hlam, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h0, h9290, h9590, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h6311, hlam, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h0, h9290, h9590, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h9290, h9590, hc01, hc12, hlam, hphi, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [hlam, p9603_0]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h6310, h9290, h9589, h9590, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h9290, hlam, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h9288, h9290, h9590, h9591, h9601, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h6310, hlam, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h9289, hlam, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [hlam, p9603_0]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h9566, hlam, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h9568, hlam, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h6310, h9589, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9603_1, u0elo3]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h0, h6310, h9290, h9589, h9590, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        rcases p9603_3 (m.d 0 1) (by simp) with h9621 | h9621
                                        · linarith only [h6311, h9621, hlam]
                                        · linarith only [h6310, h9621, hlam]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [hlam, p9603_0]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        rcases p9603_3 (m.d 0 1) (by simp) with h9625 | h9625
                                        · linarith only [h6311, h9625, hlam]
                                        · linarith only [h9288, h9625, hlam]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h9288, hlam, p9603_0]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h9565, hlam, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h6310, h6311, h9288, h9589, h9592, hc23, hc34, hlam, hphi, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [h9588, hlam, p9603_1]
                                      · have p9603_0 := h9603c.1
                                        have p9603_1 := h9603c.2.1
                                        have p9603_2 := h9603c.2.2.1
                                        have p9603_3 := h9603c.2.2.2
                                        linarith only [hlam, p9603_0]
                                    · linarith only [h6310, h6311, h9589, h9592, h9602, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h0, h9288, h9290, h9596, h9601, hlam]
                            · linarith only [h0, h9288, h9290, h9589, h9590, h9594, h9596, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h9290, h9565, h9591, hc12, hc24, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9637 | h9637
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9638 | h9638
                        · linarith only [h0, h6310, h9566, h9590, h9638, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9640 | h9640
                          · linarith only [h6310, h9568, h9640, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9642 | h9642
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9643 | h9643
                              · linarith only [h0, h9288, h9589, h9590, h9638, h9640, h9643, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h9288, h9589, h9590, h9640, h9643, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h9288, h9589, h9590, h9640, h9642, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h9565, h9637, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h9289, h9589, hlam]
                · linarith only [h0, h9288, h9290, h9588, hlam]
          · linarith only [h0, h9288, h9565, hlam]
      · linarith only [h0, h6310, h9289, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h9652 | h9652
      · rcases m.htr 0 2 4 (by decide) (by decide) with h9653 | h9653
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9654 | h9654
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9655 | h9655
            · linarith only [h6310, h6311, h9655, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9657 | h9657
              · linarith only [h6310, h9288, h9657, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9659 | h9659
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9660 | h9660
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9661 | h9661
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9662 | h9662
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9663 | h9663
                        · linarith only [h6310, h9655, h9663, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9665 | h9665
                          · linarith only [h6310, h9288, h9657, h9665, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9667 | h9667
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9668 | h9668
                              · linarith only [h6310, h9288, h9652, h9663, h9667, h9668, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9670 | h9670
                                · linarith only [h6310, h9288, h9660, h9665, h9670, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9672 | h9672
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9673 | h9673
                                    · rcases h0bigk with h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c | h9674c
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [hlam, p9674_0]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h0, hlam, p9674_1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h9288, h9663, h9667, hc03, hc34, hlam, hphi, p9674_1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h6311, hlam, p9674_1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h9288, hlam, p9674_1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h6310, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p9674_1, u0elo1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [hlam, p9674_0]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        rcases p9674_3 (m.d 0 1) (by simp) with h9682 | h9682
                                        · linarith only [h0, h9682, hlam]
                                        · linarith only [h6310, h9682, hlam]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h6310, h9288, h9659, h9660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9674_1, u0elo1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h6310, h9288, h9660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9674_1, u0elo1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h6310, hlam, p9674_1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h9652, hlam, p9674_1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [hlam, p9674_0]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h9655, hlam, p9674_1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h9657, hlam, p9674_1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h6310, h9660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9674_1, u0elo3]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h9653, hlam, p9674_0]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        rcases p9674_3 (m.d 0 1) (by simp) with h9694 | h9694
                                        · linarith only [h6311, h9694, hlam]
                                        · linarith only [h6310, h9694, hlam]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [hlam, p9674_0]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h6310, h9288, h9653, h9660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9674_1, u0elo1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h6310, h9660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9674_1, u0elo4]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h9654, hlam, p9674_1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        rcases p9674_3 (m.d 0 1) (by simp) with h9701 | h9701
                                        · linarith only [h9288, h9701, hlam]
                                        · linarith only [h6310, h9701, hlam]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [h9659, hlam, p9674_1]
                                      · have p9674_0 := h9674c.1
                                        have p9674_1 := h9674c.2.1
                                        have p9674_2 := h9674c.2.2.1
                                        have p9674_3 := h9674c.2.2.2
                                        linarith only [hlam, p9674_0]
                                    · linarith only [h6311, h9653, h9663, h9672, h9673, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9707 | h9707
                                    · rcases h0bigk with h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c | h9708c
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [hlam, p9708_0]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h0, hlam, p9708_1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h6310, h6311, h9660, h9663, hc23, hc34, hlam, hphi, p9708_1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h6311, hlam, p9708_1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h9288, hlam, p9708_1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h6310, h9660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9708_1, u0elo1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [hlam, p9708_0]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        rcases p9708_3 (m.d 0 1) (by simp) with h9716 | h9716
                                        · linarith only [h0, h9716, hlam]
                                        · linarith only [h6310, h9716, hlam]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h9659, h9672, hc24, hlam, hphi, ht0b, ht45, ht5b, p9708_1, u0elo1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h6310, h9288, h9660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9708_1, u0elo1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h6310, hlam, p9708_1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h9652, hlam, p9708_1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [hlam, p9708_0]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h9655, hlam, p9708_1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h9657, hlam, p9708_1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h6310, h9660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9708_1, u0elo3]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h9653, hlam, p9708_0]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        rcases p9708_3 (m.d 0 1) (by simp) with h9728 | h9728
                                        · linarith only [h6311, h9728, hlam]
                                        · linarith only [h6310, h9728, hlam]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [hlam, p9708_0]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h6310, h9288, h9660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9708_1, u0elo3]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h6310, h9660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9708_1, u0elo4]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h9654, hlam, p9708_1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        rcases p9708_3 (m.d 0 1) (by simp) with h9735 | h9735
                                        · linarith only [h9288, h9735, hlam]
                                        · linarith only [h6310, h9735, hlam]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [h9659, hlam, p9708_1]
                                      · have p9708_0 := h9708c.1
                                        have p9708_1 := h9708c.2.1
                                        have p9708_2 := h9708c.2.2.1
                                        have p9708_3 := h9708c.2.2.2
                                        linarith only [hlam, p9708_0]
                                    · linarith only [h9655, h9659, h9707, hlam]
                            · linarith only [h6311, h9659, h9667, hlam]
                      · linarith only [h0, h9654, h9662, hlam]
                    · linarith only [h0, h9653, h9661, hlam]
                  · linarith only [h0, h9652, h9660, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9745 | h9745
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9746 | h9746
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9747 | h9747
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9748 | h9748
                        · linarith only [h6310, h6311, h9659, h9748, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9750 | h9750
                          · linarith only [h6310, h9288, h9657, h9750, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9752 | h9752
                            · linarith only [h6310, h6311, h9659, h9748, h9752, hc13, hc34, hlam, hphi]
                            · linarith only [h6310, h6311, h9745, h9752, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h6310, h9654, h9745, h9747, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h6310, h9653, h9745, h9746, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h9652, h9745, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9758 | h9758
            · linarith only [h6310, h6311, h9758, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9760 | h9760
              · linarith only [h6310, h9288, h9760, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9762 | h9762
                · linarith only [h9653, h9654, h9762, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9764 | h9764
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9765 | h9765
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9766 | h9766
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9767 | h9767
                        · linarith only [h6310, h9758, h9767, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9769 | h9769
                          · linarith only [h6310, h6311, h9653, h9654, h9760, h9769, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9771 | h9771
                            · linarith only [h6310, h6311, h9762, h9764, h9767, h9771, hc23, hc34, hlam, hphi]
                            · linarith only [h6310, h6311, h9764, h9771, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9774 | h9774
                        · linarith only [h6310, h6311, h9765, h9766, h9774, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9776 | h9776
                          · linarith only [h6310, h6311, h9765, h9766, h9776, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9778 | h9778
                            · linarith only [h6310, h6311, h9762, h9764, h9765, h9766, h9778, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · linarith only [h6310, h6311, h9764, h9778, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6310, h9653, h9764, h9765, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h9652, h9764, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9783 | h9783
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9784 | h9784
            · linarith only [h0, h6310, h9653, h9784, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9786 | h9786
              · linarith only [h6310, h9288, h9786, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9788 | h9788
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9789 | h9789
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9790 | h9790
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9791 | h9791
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9792 | h9792
                        · linarith only [h6310, h9784, h9792, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9794 | h9794
                          · linarith only [h6310, h9288, h9786, h9794, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9796 | h9796
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9797 | h9797
                              · linarith only [h9652, h9653, h9790, h9792, h9797, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9799 | h9799
                                · linarith only [h6310, h9288, h9789, h9794, h9799, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9801 | h9801
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9802 | h9802
                                    · rcases h0bigk with h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c | h9803c
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [hlam, p9803_0]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h0, hlam, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h9288, h9653, h9783, h9790, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h6311, hlam, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h9288, hlam, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h9653, h9790, hc01, hc12, hlam, hphi, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [hlam, p9803_0]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h6310, h9653, h9789, h9790, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h9653, hlam, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h9653, h9790, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h6310, hlam, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h9652, hlam, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [hlam, p9803_0]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h9784, hlam, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h9786, hlam, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h6310, h9789, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9803_1, u0elo3]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h0, h6310, h9653, h9789, h9790, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        rcases p9803_3 (m.d 0 1) (by simp) with h9821 | h9821
                                        · linarith only [h6311, h9821, hlam]
                                        · linarith only [h6310, h9821, hlam]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [hlam, p9803_0]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h6310, h9288, h9653, h9789, h9790, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h6310, h9783, h9789, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9803_1, u0elo1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h9783, hlam, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h6310, h9653, h9783, h9789, h9790, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [h9788, hlam, p9803_1]
                                      · have p9803_0 := h9803c.1
                                        have p9803_1 := h9803c.2.1
                                        have p9803_2 := h9803c.2.2.1
                                        have p9803_3 := h9803c.2.2.2
                                        linarith only [hlam, p9803_0]
                                    · linarith only [h0, h6310, h9653, h9789, h9790, h9792, h9802, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h9653, h9783, h9788, h9801, hlam]
                            · linarith only [h9653, h9783, h9788, h9790, h9796, hlam]
                      · linarith only [h9653, h9783, h9791, hc12, hc24, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9835 | h9835
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9836 | h9836
                        · linarith only [h6310, h9288, h9790, h9835, h9836, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9838 | h9838
                          · linarith only [h6310, h9288, h9790, h9835, h9838, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9840 | h9840
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9841 | h9841
                              · linarith only [h6310, h6311, h9288, h9789, h9790, h9835, h9836, h9841, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h6310, h9288, h9790, h9835, h9841, hc13, hc34, hlam, hphi]
                            · linarith only [h6310, h9288, h9788, h9789, h9790, h9835, h9840, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h6310, h9783, h9789, h9835, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h9652, h9789, hlam]
                · linarith only [h9653, h9783, h9788, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9848 | h9848
            · linarith only [h0, h6310, h9653, h9848, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9850 | h9850
              · linarith only [h6310, h9288, h9850, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9852 | h9852
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9853 | h9853
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9854 | h9854
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9855 | h9855
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9856 | h9856
                        · linarith only [h0, h6310, h9653, h9848, h9854, h9856, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9858 | h9858
                          · linarith only [h0, h6310, h9783, h9850, h9858, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9860 | h9860
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9861 | h9861
                              · linarith only [h9652, h9783, h9855, h9856, h9860, h9861, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9863 | h9863
                                · linarith only [h0, h6310, h9783, h9853, h9855, h9858, h9863, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9865 | h9865
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9866 | h9866
                                    · rcases h0bigk with h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c | h9867c
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [hlam, p9867_0]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h0, hlam, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h0, h9783, h9854, h9865, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h6311, hlam, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h9288, hlam, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h9783, h9854, h9865, hc01, hc12, hlam, hphi, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [hlam, p9867_0]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h6310, h9783, h9853, h9854, h9865, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h9653, hlam, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h9783, hlam, p9867_0]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h6310, hlam, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h9652, hlam, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [hlam, p9867_0]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h9848, hlam, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h9850, hlam, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h6310, h9853, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9867_1, u0elo3]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h0, h6310, h9653, h9853, h9854, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        rcases p9867_3 (m.d 0 1) (by simp) with h9885 | h9885
                                        · linarith only [h6311, h9885, hlam]
                                        · linarith only [h6310, h9885, hlam]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [hlam, p9867_0]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h6310, h9288, h9653, h9853, h9854, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h6310, h9853, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9867_1, u0elo4]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h0, h6310, h9783, h9853, h9854, h9865, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        rcases p9867_3 (m.d 0 1) (by simp) with h9892 | h9892
                                        · linarith only [h9288, h9892, hlam]
                                        · linarith only [h6310, h9892, hlam]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [h9852, hlam, p9867_1]
                                      · have p9867_0 := h9867c.1
                                        have p9867_1 := h9867c.2.1
                                        have p9867_2 := h9867c.2.2.1
                                        have p9867_3 := h9867c.2.2.2
                                        linarith only [hlam, p9867_0]
                                    · linarith only [h9653, h9852, h9854, h9856, h9866, hlam]
                                  · linarith only [h9653, h9852, h9865, hlam]
                            · linarith only [h9653, h9852, h9854, h9860, hlam]
                      · linarith only [h0, h6310, h9653, h9853, h9854, h9855, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9901 | h9901
                      · linarith only [h0, h6310, h9783, h9853, h9854, h9901, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9903 | h9903
                        · linarith only [h0, h6310, h9854, h9903, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9905 | h9905
                          · linarith only [h0, h6310, h9850, h9854, h9905, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9907 | h9907
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9908 | h9908
                              · linarith only [h0, h6310, h6311, h9853, h9854, h9903, h9908, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h6310, h9853, h9854, h9908, hc23, hc34, hlam, hphi]
                            · linarith only [h6310, h6311, h9852, h9853, h9907, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h6310, h9652, h9853, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9913 | h9913
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9914 | h9914
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9915 | h9915
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9916 | h9916
                        · linarith only [h0, h6310, h9653, h9914, h9916, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9918 | h9918
                          · linarith only [h0, h6310, h9653, h9914, h9918, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9920 | h9920
                            · linarith only [h6310, h6311, h9852, h9913, h9916, h9920, hc23, hc34, hlam, hphi]
                            · linarith only [h6310, h6311, h9913, h9920, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h6310, h9653, h9913, h9914, h9915, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9924 | h9924
                      · linarith only [h0, h6310, h9783, h9913, h9914, h9924, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9926 | h9926
                        · linarith only [h0, h6310, h9914, h9926, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9928 | h9928
                          · linarith only [h0, h6310, h9914, h9928, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9930 | h9930
                            · linarith only [h0, h6310, h9653, h9852, h9913, h9926, h9930, hc23, hc34, hlam, hphi]
                            · linarith only [h6310, h6311, h9913, h9930, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h9652, h9913, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h6310, h9652, hlam]

end R2N4
